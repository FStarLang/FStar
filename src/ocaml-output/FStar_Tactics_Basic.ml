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
                 let uu___98_1026 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___98_1026.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___98_1026.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___98_1026.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___98_1026.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___98_1026.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___98_1026.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___98_1026.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___98_1026.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___98_1026.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___98_1026.FStar_Tactics_Types.guard_policy);
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
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___103_1314 = ps  in
         let uu____1315 =
           FStar_List.filter
             (fun g  ->
                let uu____1321 = check_goal_solved g  in
                FStar_Option.isNone uu____1321) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___103_1314.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___103_1314.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___103_1314.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1315;
           FStar_Tactics_Types.smt_goals =
             (uu___103_1314.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___103_1314.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___103_1314.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___103_1314.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___103_1314.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___103_1314.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___103_1314.FStar_Tactics_Types.freshness)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1338 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1338 with
      | FStar_Pervasives_Native.Some uu____1343 ->
          let uu____1344 =
            let uu____1345 = goal_to_string goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1345  in
          fail uu____1344
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1361 = FStar_Tactics_Types.goal_env goal  in
      let uu____1362 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1361 solution uu____1362
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1368 =
         let uu___104_1369 = p  in
         let uu____1370 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___104_1369.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___104_1369.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___104_1369.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1370;
           FStar_Tactics_Types.smt_goals =
             (uu___104_1369.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___104_1369.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___104_1369.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___104_1369.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___104_1369.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___104_1369.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___104_1369.FStar_Tactics_Types.freshness)
         }  in
       set uu____1368)
  
let (dismiss : unit -> unit tac) =
  fun uu____1379  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1386 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1403 = trysolve goal solution  in
      bind uu____1403
        (fun b  ->
           if b
           then bind __dismiss (fun uu____1411  -> remove_solved_goals)
           else
             (let uu____1413 =
                let uu____1414 =
                  let uu____1415 = FStar_Tactics_Types.goal_env goal  in
                  tts uu____1415 solution  in
                let uu____1416 =
                  let uu____1417 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1418 = FStar_Tactics_Types.goal_witness goal  in
                  tts uu____1417 uu____1418  in
                let uu____1419 =
                  let uu____1420 = FStar_Tactics_Types.goal_env goal  in
                  let uu____1421 = FStar_Tactics_Types.goal_type goal  in
                  tts uu____1420 uu____1421  in
                FStar_Util.format3 "%s does not solve %s : %s" uu____1414
                  uu____1416 uu____1419
                 in
              fail uu____1413))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1436 = set_solution goal solution  in
      bind uu____1436
        (fun uu____1440  ->
           bind __dismiss (fun uu____1442  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___105_1449 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___105_1449.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___105_1449.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___105_1449.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___105_1449.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___105_1449.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___105_1449.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___105_1449.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___105_1449.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___105_1449.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___105_1449.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1468 = FStar_Options.defensive ()  in
    if uu____1468
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1473 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1473)
         in
      let b2 =
        b1 &&
          (let uu____1476 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1476)
         in
      let rec aux b3 e =
        let uu____1488 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1488 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1506 =
        (let uu____1509 = aux b2 env  in Prims.op_Negation uu____1509) &&
          (let uu____1511 = FStar_ST.op_Bang nwarn  in
           uu____1511 < (Prims.parse_int "5"))
         in
      (if uu____1506
       then
         ((let uu____1536 =
             let uu____1537 = FStar_Tactics_Types.goal_type g  in
             uu____1537.FStar_Syntax_Syntax.pos  in
           let uu____1540 =
             let uu____1545 =
               let uu____1546 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1546
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1545)  in
           FStar_Errors.log_issue uu____1536 uu____1540);
          (let uu____1547 =
             let uu____1548 = FStar_ST.op_Bang nwarn  in
             uu____1548 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1547))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___106_1616 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___106_1616.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___106_1616.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___106_1616.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___106_1616.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___106_1616.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___106_1616.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___106_1616.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___106_1616.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___106_1616.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___106_1616.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___107_1636 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___107_1636.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___107_1636.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___107_1636.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___107_1636.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___107_1636.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___107_1636.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___107_1636.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___107_1636.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___107_1636.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___107_1636.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___108_1656 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_1656.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_1656.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___108_1656.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___108_1656.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_1656.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_1656.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_1656.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_1656.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___108_1656.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___108_1656.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___109_1676 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___109_1676.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___109_1676.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___109_1676.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___109_1676.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___109_1676.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___109_1676.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___109_1676.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___109_1676.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___109_1676.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___109_1676.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1687  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___110_1701 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___110_1701.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___110_1701.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___110_1701.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___110_1701.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___110_1701.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___110_1701.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___110_1701.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___110_1701.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___110_1701.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___110_1701.FStar_Tactics_Types.freshness)
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
        let uu____1739 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1739 with
        | (u,ctx_uvar,g_u) ->
            let uu____1773 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1773
              (fun uu____1782  ->
                 let uu____1783 =
                   let uu____1788 =
                     let uu____1789 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1789  in
                   (u, uu____1788)  in
                 ret uu____1783)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1807 = FStar_Syntax_Util.un_squash t  in
    match uu____1807 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1817 =
          let uu____1818 = FStar_Syntax_Subst.compress t'  in
          uu____1818.FStar_Syntax_Syntax.n  in
        (match uu____1817 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1822 -> false)
    | uu____1823 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1833 = FStar_Syntax_Util.un_squash t  in
    match uu____1833 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1843 =
          let uu____1844 = FStar_Syntax_Subst.compress t'  in
          uu____1844.FStar_Syntax_Syntax.n  in
        (match uu____1843 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1848 -> false)
    | uu____1849 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1860  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1871 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1871 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1878 = goal_to_string hd1  in
                    let uu____1879 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1878 uu____1879);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1886  ->
    let uu____1889 =
      let uu____1892 = cur_goal ()  in
      bind uu____1892
        (fun g  ->
           (let uu____1899 =
              let uu____1900 = FStar_Tactics_Types.goal_type g  in
              uu____1900.FStar_Syntax_Syntax.pos  in
            let uu____1903 =
              let uu____1908 =
                let uu____1909 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1909
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1908)  in
            FStar_Errors.log_issue uu____1899 uu____1903);
           solve' g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1889
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1920  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___111_1930 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___111_1930.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___111_1930.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___111_1930.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___111_1930.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___111_1930.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___111_1930.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___111_1930.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___111_1930.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___111_1930.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___111_1930.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1931 = set ps1  in
         bind uu____1931
           (fun uu____1936  ->
              let uu____1937 = FStar_BigInt.of_int_fs n1  in ret uu____1937))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1944  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1952 = FStar_BigInt.of_int_fs n1  in ret uu____1952)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1965  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1973 = FStar_BigInt.of_int_fs n1  in ret uu____1973)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1986  ->
    let uu____1989 = cur_goal ()  in
    bind uu____1989 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2021 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2021 phi  in
          let uu____2022 = new_uvar reason env typ  in
          bind uu____2022
            (fun uu____2037  ->
               match uu____2037 with
               | (uu____2044,ctx_uvar) ->
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
             (fun uu____2089  ->
                let uu____2090 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2090)
             (fun uu____2092  ->
                try
                  let uu____2112 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____2112
                with
                | FStar_Errors.Err (uu____2139,msg) ->
                    let uu____2141 = tts e t  in
                    let uu____2142 =
                      let uu____2143 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2143
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2141 uu____2142 msg
                | FStar_Errors.Error (uu____2150,msg,uu____2152) ->
                    let uu____2153 = tts e t  in
                    let uu____2154 =
                      let uu____2155 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2155
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2153 uu____2154 msg))
  
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
  fun uu____2182  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___114_2200 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___114_2200.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___114_2200.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___114_2200.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___114_2200.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___114_2200.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___114_2200.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___114_2200.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___114_2200.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___114_2200.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___114_2200.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2224 = get_guard_policy ()  in
      bind uu____2224
        (fun old_pol  ->
           let uu____2230 = set_guard_policy pol  in
           bind uu____2230
             (fun uu____2234  ->
                bind t
                  (fun r  ->
                     let uu____2238 = set_guard_policy old_pol  in
                     bind uu____2238 (fun uu____2242  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2267 =
            let uu____2268 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2268.FStar_TypeChecker_Env.guard_f  in
          match uu____2267 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2272 = istrivial e f  in
              if uu____2272
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2280 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2280
                           (fun goal  ->
                              let goal1 =
                                let uu___115_2287 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___115_2287.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___115_2287.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___115_2287.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2288 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2288
                           (fun goal  ->
                              let goal1 =
                                let uu___116_2295 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___116_2295.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___116_2295.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___116_2295.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2303 =
                              let uu____2304 =
                                let uu____2305 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2305
                                 in
                              Prims.op_Negation uu____2304  in
                            if uu____2303
                            then
                              mlog
                                (fun uu____2310  ->
                                   let uu____2311 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2311)
                                (fun uu____2313  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2320 ->
                              mlog
                                (fun uu____2323  ->
                                   let uu____2324 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2324)
                                (fun uu____2326  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2336 =
      let uu____2339 = cur_goal ()  in
      bind uu____2339
        (fun goal  ->
           let uu____2345 =
             let uu____2354 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2354 t  in
           bind uu____2345
             (fun uu____2366  ->
                match uu____2366 with
                | (t1,typ,guard) ->
                    let uu____2378 =
                      let uu____2381 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2381 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2378 (fun uu____2383  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2336
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2412 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2412 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2423  ->
    let uu____2426 = cur_goal ()  in
    bind uu____2426
      (fun goal  ->
         let uu____2432 =
           let uu____2433 = FStar_Tactics_Types.goal_env goal  in
           let uu____2434 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2433 uu____2434  in
         if uu____2432
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2438 =
              let uu____2439 = FStar_Tactics_Types.goal_env goal  in
              let uu____2440 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2439 uu____2440  in
            fail1 "Not a trivial goal: %s" uu____2438))
  
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
          let uu____2469 =
            let uu____2470 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2470.FStar_TypeChecker_Env.guard_f  in
          match uu____2469 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2478 = istrivial e f  in
              if uu____2478
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2486 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2486
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___119_2496 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___119_2496.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___119_2496.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___119_2496.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2503  ->
    let uu____2506 = cur_goal ()  in
    bind uu____2506
      (fun g  ->
         let uu____2512 = is_irrelevant g  in
         if uu____2512
         then bind __dismiss (fun uu____2516  -> add_smt_goals [g])
         else
           (let uu____2518 =
              let uu____2519 = FStar_Tactics_Types.goal_env g  in
              let uu____2520 = FStar_Tactics_Types.goal_type g  in
              tts uu____2519 uu____2520  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2518))
  
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
             let uu____2569 =
               try
                 let uu____2603 =
                   let uu____2612 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2612 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2603
               with | uu____2634 -> fail "divide: not enough goals"  in
             bind uu____2569
               (fun uu____2661  ->
                  match uu____2661 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___120_2687 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___120_2687.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___120_2687.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___120_2687.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___120_2687.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___120_2687.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___120_2687.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___120_2687.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___120_2687.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___120_2687.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___121_2689 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___121_2689.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___121_2689.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___121_2689.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___121_2689.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___121_2689.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___121_2689.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___121_2689.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___121_2689.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___121_2689.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2690 = set lp  in
                      bind uu____2690
                        (fun uu____2698  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2712 = set rp  in
                                     bind uu____2712
                                       (fun uu____2720  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___122_2736 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___122_2736.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___122_2736.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2737 = set p'
                                                       in
                                                    bind uu____2737
                                                      (fun uu____2745  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2751 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2772 = divide FStar_BigInt.one f idtac  in
    bind uu____2772
      (fun uu____2785  -> match uu____2785 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2822::uu____2823 ->
             let uu____2826 =
               let uu____2835 = map tau  in
               divide FStar_BigInt.one tau uu____2835  in
             bind uu____2826
               (fun uu____2853  ->
                  match uu____2853 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2894 =
        bind t1
          (fun uu____2899  ->
             let uu____2900 = map t2  in
             bind uu____2900 (fun uu____2908  -> ret ()))
         in
      focus uu____2894
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2917  ->
    let uu____2920 =
      let uu____2923 = cur_goal ()  in
      bind uu____2923
        (fun goal  ->
           let uu____2932 =
             let uu____2939 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2939  in
           match uu____2932 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2948 =
                 let uu____2949 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2949  in
               if uu____2948
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2954 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2954 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2964 = new_uvar "intro" env' typ'  in
                  bind uu____2964
                    (fun uu____2980  ->
                       match uu____2980 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3000 = set_solution goal sol  in
                           bind uu____3000
                             (fun uu____3006  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3008 = replace_cur g  in
                                bind uu____3008 (fun uu____3012  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3017 =
                 let uu____3018 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3019 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3018 uu____3019  in
               fail1 "goal is not an arrow (%s)" uu____3017)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2920
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3034  ->
    let uu____3041 = cur_goal ()  in
    bind uu____3041
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3058 =
            let uu____3065 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3065  in
          match uu____3058 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3078 =
                let uu____3079 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3079  in
              if uu____3078
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3092 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3092
                    in
                 let bs =
                   let uu____3100 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3100; b]  in
                 let env' =
                   let uu____3118 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3118 bs  in
                 let uu____3119 =
                   let uu____3126 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3126  in
                 bind uu____3119
                   (fun uu____3145  ->
                      match uu____3145 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3159 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3162 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3159
                              FStar_Parser_Const.effect_Tot_lid uu____3162 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3176 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3176 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3198 =
                                   let uu____3199 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3199.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3198
                                  in
                               let uu____3212 = set_solution goal tm  in
                               bind uu____3212
                                 (fun uu____3221  ->
                                    let uu____3222 =
                                      replace_cur
                                        (let uu___125_3227 = goal  in
                                         {
                                           FStar_Tactics_Types.goal_main_env
                                             =
                                             (uu___125_3227.FStar_Tactics_Types.goal_main_env);
                                           FStar_Tactics_Types.goal_ctx_uvar
                                             = ctx_uvar_u;
                                           FStar_Tactics_Types.opts =
                                             (uu___125_3227.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___125_3227.FStar_Tactics_Types.is_guard)
                                         })
                                       in
                                    bind uu____3222
                                      (fun uu____3234  ->
                                         let uu____3235 =
                                           let uu____3240 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3240, b)  in
                                         ret uu____3235)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3249 =
                let uu____3250 = FStar_Tactics_Types.goal_env goal  in
                let uu____3251 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3250 uu____3251  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3249))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3269 = cur_goal ()  in
    bind uu____3269
      (fun goal  ->
         mlog
           (fun uu____3276  ->
              let uu____3277 =
                let uu____3278 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3278  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3277)
           (fun uu____3283  ->
              let steps =
                let uu____3287 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3287
                 in
              let t =
                let uu____3291 = FStar_Tactics_Types.goal_env goal  in
                let uu____3292 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3291 uu____3292  in
              let uu____3293 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3293))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3317 =
          mlog
            (fun uu____3322  ->
               let uu____3323 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3323)
            (fun uu____3325  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3331 -> g.FStar_Tactics_Types.opts
                      | uu____3334 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3339  ->
                         let uu____3340 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3340)
                      (fun uu____3343  ->
                         let uu____3344 = __tc e t  in
                         bind uu____3344
                           (fun uu____3365  ->
                              match uu____3365 with
                              | (t1,uu____3375,uu____3376) ->
                                  let steps =
                                    let uu____3380 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3380
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3317
  
let (refine_intro : unit -> unit tac) =
  fun uu____3394  ->
    let uu____3397 =
      let uu____3400 = cur_goal ()  in
      bind uu____3400
        (fun g  ->
           let uu____3407 =
             let uu____3418 = FStar_Tactics_Types.goal_env g  in
             let uu____3419 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3418 uu____3419
              in
           match uu____3407 with
           | (uu____3422,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3447 =
                 let uu____3452 =
                   let uu____3457 =
                     let uu____3458 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3458]  in
                   FStar_Syntax_Subst.open_term uu____3457 phi  in
                 match uu____3452 with
                 | (bvs,phi1) ->
                     let uu____3477 =
                       let uu____3478 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3478  in
                     (uu____3477, phi1)
                  in
               (match uu____3447 with
                | (bv1,phi1) ->
                    let uu____3491 =
                      let uu____3494 = FStar_Tactics_Types.goal_env g  in
                      let uu____3495 =
                        let uu____3496 =
                          let uu____3499 =
                            let uu____3500 =
                              let uu____3507 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3507)  in
                            FStar_Syntax_Syntax.NT uu____3500  in
                          [uu____3499]  in
                        FStar_Syntax_Subst.subst uu____3496 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3494
                        uu____3495 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3491
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3515  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3397
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3534 = cur_goal ()  in
      bind uu____3534
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3542 = FStar_Tactics_Types.goal_env goal  in
               let uu____3543 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3542 uu____3543
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3545 = __tc env t  in
           bind uu____3545
             (fun uu____3564  ->
                match uu____3564 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3579  ->
                         let uu____3580 =
                           let uu____3581 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3581 typ  in
                         let uu____3582 =
                           let uu____3583 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3583
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now and guard %s\n"
                           uu____3580 uu____3582)
                      (fun uu____3586  ->
                         let uu____3587 =
                           let uu____3590 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3590 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3587
                           (fun uu____3592  ->
                              mlog
                                (fun uu____3596  ->
                                   let uu____3597 =
                                     let uu____3598 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3598 typ  in
                                   let uu____3599 =
                                     let uu____3600 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3601 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3600 uu____3601  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3597 uu____3599)
                                (fun uu____3604  ->
                                   let uu____3605 =
                                     let uu____3608 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3609 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3608 typ uu____3609  in
                                   bind uu____3605
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3615 =
                                             let uu____3616 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3616 t1  in
                                           let uu____3617 =
                                             let uu____3618 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3618 typ  in
                                           let uu____3619 =
                                             let uu____3620 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3621 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3620 uu____3621  in
                                           let uu____3622 =
                                             let uu____3623 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3624 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3623 uu____3624  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3615 uu____3617 uu____3619
                                             uu____3622)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3639 =
        mlog
          (fun uu____3644  ->
             let uu____3645 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3645)
          (fun uu____3648  ->
             let uu____3649 =
               let uu____3656 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3656  in
             bind uu____3649
               (fun uu___93_3665  ->
                  match uu___93_3665 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      let uu____3674 =
                        let uu____3681 =
                          let uu____3684 =
                            norm [FStar_Syntax_Embeddings.Delta]  in
                          bind uu____3684
                            (fun uu____3689  ->
                               let uu____3690 = refine_intro ()  in
                               bind uu____3690
                                 (fun uu____3694  ->
                                    __exact_now set_expected_typ1 tm))
                           in
                        trytac' uu____3681  in
                      bind uu____3674
                        (fun uu___92_3701  ->
                           match uu___92_3701 with
                           | FStar_Util.Inr r -> ret ()
                           | FStar_Util.Inl uu____3709 -> fail e)))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3639
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3738 =
             let uu____3741 =
               let uu____3744 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3744  in
             FStar_Util.set_elements uu____3741  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3738
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
          let uu____3822 = f x  in
          bind uu____3822
            (fun y  ->
               let uu____3830 = mapM f xs  in
               bind uu____3830 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3850 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3870 = cur_goal ()  in
        bind uu____3870
          (fun goal  ->
             mlog
               (fun uu____3877  ->
                  let uu____3878 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3878)
               (fun uu____3881  ->
                  let uu____3882 =
                    let uu____3887 =
                      let uu____3890 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3890  in
                    trytac_exn uu____3887  in
                  bind uu____3882
                    (fun uu___94_3897  ->
                       match uu___94_3897 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3905  ->
                                let uu____3906 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3906)
                             (fun uu____3909  ->
                                let uu____3910 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3910 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3934  ->
                                         let uu____3935 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3935)
                                      (fun uu____3938  ->
                                         let uu____3939 =
                                           let uu____3940 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3940  in
                                         if uu____3939
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3944 =
                                              let uu____3951 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3951
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3944
                                              (fun uu____3962  ->
                                                 match uu____3962 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____3989 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____3989
                                                        in
                                                     let uu____3992 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____3992
                                                       (fun uu____4000  ->
                                                          let u1 =
                                                            let uu____4002 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4002
                                                              u
                                                             in
                                                          let uu____4003 =
                                                            let uu____4004 =
                                                              let uu____4007
                                                                =
                                                                let uu____4008
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4008
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4007
                                                               in
                                                            uu____4004.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4003
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4036)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4060
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4060
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    add_goals
                                                                    [(
                                                                    let uu___126_4065
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___126_4065.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___126_4065.FStar_Tactics_Types.opts);
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
      let uu____4120 =
        mlog
          (fun uu____4125  ->
             let uu____4126 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4126)
          (fun uu____4129  ->
             let uu____4130 = cur_goal ()  in
             bind uu____4130
               (fun goal  ->
                  let uu____4136 =
                    let uu____4145 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4145 tm  in
                  bind uu____4136
                    (fun uu____4159  ->
                       match uu____4159 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4172 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4172 typ  in
                           let uu____4173 =
                             let uu____4176 =
                               let uu____4179 = __apply uopt tm1 typ1  in
                               bind uu____4179
                                 (fun uu____4184  ->
                                    let uu____4185 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4185 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4176  in
                           let uu____4186 =
                             let uu____4189 =
                               let uu____4190 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4190 tm1  in
                             let uu____4191 =
                               let uu____4192 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4192 typ1  in
                             let uu____4193 =
                               let uu____4194 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4195 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4194 uu____4195  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4189 uu____4191 uu____4193
                              in
                           try_unif uu____4173 uu____4186)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4120
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4218 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4218
    then
      let uu____4225 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4244 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4285 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4225 with
      | (pre,post) ->
          let post1 =
            let uu____4321 =
              let uu____4330 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4330]  in
            FStar_Syntax_Util.mk_app post uu____4321  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4354 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4354
       then
         let uu____4361 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4361
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4394 =
      let uu____4397 =
        mlog
          (fun uu____4402  ->
             let uu____4403 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4403)
          (fun uu____4407  ->
             let is_unit_t t =
               let uu____4414 =
                 let uu____4415 = FStar_Syntax_Subst.compress t  in
                 uu____4415.FStar_Syntax_Syntax.n  in
               match uu____4414 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4419 -> false  in
             let uu____4420 = cur_goal ()  in
             bind uu____4420
               (fun goal  ->
                  let uu____4426 =
                    let uu____4435 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4435 tm  in
                  bind uu____4426
                    (fun uu____4450  ->
                       match uu____4450 with
                       | (tm1,t,guard) ->
                           let uu____4462 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4462 with
                            | (bs,comp) ->
                                let uu____4489 = lemma_or_sq comp  in
                                (match uu____4489 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4508 =
                                       FStar_List.fold_left
                                         (fun uu____4550  ->
                                            fun uu____4551  ->
                                              match (uu____4550, uu____4551)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4642 =
                                                    is_unit_t b_t  in
                                                  if uu____4642
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4678 =
                                                       let uu____4691 =
                                                         let uu____4692 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4692.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4695 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4691
                                                         uu____4695 b_t
                                                        in
                                                     match uu____4678 with
                                                     | (u,uu____4711,g_u) ->
                                                         let uu____4725 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4725,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4508 with
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
                                          let uu____4786 =
                                            let uu____4789 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4790 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4791 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4789 uu____4790
                                              uu____4791
                                             in
                                          bind uu____4786
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4799 =
                                                   let uu____4800 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4800 tm1  in
                                                 let uu____4801 =
                                                   let uu____4802 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4803 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4802 uu____4803
                                                    in
                                                 let uu____4804 =
                                                   let uu____4805 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4806 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4805 uu____4806
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4799 uu____4801
                                                   uu____4804
                                               else
                                                 (let uu____4808 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4808
                                                    (fun uu____4813  ->
                                                       let uu____4814 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4814
                                                         (fun uu____4822  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4847
                                                                  =
                                                                  let uu____4850
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4850
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4847
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
                                                                   let uu____4885
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4885)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4901
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4901
                                                              with
                                                              | (hd1,uu____4917)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4939)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4960
                                                                    -> false)
                                                               in
                                                            let uu____4961 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5031
                                                                     ->
                                                                    match uu____5031
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range,uu____5056)
                                                                    ->
                                                                    let uu____5057
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5057
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5083)
                                                                    ->
                                                                    let uu____5104
                                                                    =
                                                                    let uu____5105
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5105.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5104
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5119)
                                                                    ->
                                                                    let env =
                                                                    let uu___129_5141
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___129_5141.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let goal_ty
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let goal1
                                                                    =
                                                                    FStar_Tactics_Types.goal_with_type
                                                                    (let uu___130_5146
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___130_5146.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___130_5146.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___130_5146.FStar_Tactics_Types.is_guard)
                                                                    })
                                                                    goal_ty
                                                                     in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5159
                                                                    ->
                                                                    let env =
                                                                    let uu___131_5161
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___131_5161.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5163
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5163
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
                                                                    let uu____5166
                                                                    =
                                                                    let uu____5173
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5173
                                                                    term1  in
                                                                    match uu____5166
                                                                    with
                                                                    | 
                                                                    (uu____5174,uu____5175,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5177
                                                                    =
                                                                    let uu____5182
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5182
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5177
                                                                    (fun
                                                                    uu___95_5194
                                                                     ->
                                                                    match uu___95_5194
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
                                                            bind uu____4961
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5262
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5262
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5284
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5284
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5345
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5345
                                                                    then
                                                                    let uu____5348
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5348
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
                                                                    let uu____5362
                                                                    =
                                                                    let uu____5363
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5363
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5362)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5364
                                                                   =
                                                                   let uu____5367
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5367
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5364
                                                                   (fun
                                                                    uu____5370
                                                                     ->
                                                                    let uu____5371
                                                                    =
                                                                    let uu____5374
                                                                    =
                                                                    let uu____5375
                                                                    =
                                                                    let uu____5376
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5377
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5376
                                                                    uu____5377
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5375
                                                                     in
                                                                    if
                                                                    uu____5374
                                                                    then
                                                                    let uu____5380
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5380
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5371
                                                                    (fun
                                                                    uu____5384
                                                                     ->
                                                                    let uu____5385
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5385
                                                                    (fun
                                                                    uu____5389
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4397  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4394
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5411 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5411 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5421::(e1,uu____5423)::(e2,uu____5425)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5468 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5492 = destruct_eq' typ  in
    match uu____5492 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5522 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5522 with
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
        let uu____5584 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5584 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5632 = aux e'  in
               FStar_Util.map_opt uu____5632
                 (fun uu____5656  ->
                    match uu____5656 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5677 = aux e  in
      FStar_Util.map_opt uu____5677
        (fun uu____5701  ->
           match uu____5701 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5768 =
            let uu____5777 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5777  in
          FStar_Util.map_opt uu____5768
            (fun uu____5792  ->
               match uu____5792 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___132_5811 = bv  in
                     let uu____5812 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___132_5811.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___132_5811.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5812
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___133_5820 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5821 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5828 =
                       let uu____5831 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5831  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___133_5820.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5821;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5828;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___133_5820.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___133_5820.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___133_5820.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___134_5832 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___134_5832.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___134_5832.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___134_5832.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5842 = cur_goal ()  in
    bind uu____5842
      (fun goal  ->
         let uu____5850 = h  in
         match uu____5850 with
         | (bv,uu____5854) ->
             mlog
               (fun uu____5858  ->
                  let uu____5859 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5860 =
                    let uu____5861 = FStar_Tactics_Types.goal_env goal  in
                    tts uu____5861 bv.FStar_Syntax_Syntax.sort  in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5859
                    uu____5860)
               (fun uu____5864  ->
                  let uu____5865 =
                    let uu____5874 = FStar_Tactics_Types.goal_env goal  in
                    split_env bv uu____5874  in
                  match uu____5865 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5895 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5895 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5910 =
                             let uu____5911 = FStar_Syntax_Subst.compress x
                                in
                             uu____5911.FStar_Syntax_Syntax.n  in
                           (match uu____5910 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___135_5928 = bv1  in
                                  let uu____5929 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___135_5928.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___135_5928.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5929
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let new_env = push_bvs e0 (bv :: bvs1)  in
                                let new_goal =
                                  let uu___136_5937 =
                                    goal.FStar_Tactics_Types.goal_ctx_uvar
                                     in
                                  let uu____5938 =
                                    FStar_TypeChecker_Env.all_binders new_env
                                     in
                                  let uu____5945 =
                                    let uu____5948 =
                                      FStar_Tactics_Types.goal_type goal  in
                                    FStar_Syntax_Subst.subst s uu____5948  in
                                  {
                                    FStar_Syntax_Syntax.ctx_uvar_head =
                                      (uu___136_5937.FStar_Syntax_Syntax.ctx_uvar_head);
                                    FStar_Syntax_Syntax.ctx_uvar_gamma =
                                      (new_env.FStar_TypeChecker_Env.gamma);
                                    FStar_Syntax_Syntax.ctx_uvar_binders =
                                      uu____5938;
                                    FStar_Syntax_Syntax.ctx_uvar_typ =
                                      uu____5945;
                                    FStar_Syntax_Syntax.ctx_uvar_reason =
                                      (uu___136_5937.FStar_Syntax_Syntax.ctx_uvar_reason);
                                    FStar_Syntax_Syntax.ctx_uvar_should_check
                                      =
                                      (uu___136_5937.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                    FStar_Syntax_Syntax.ctx_uvar_range =
                                      (uu___136_5937.FStar_Syntax_Syntax.ctx_uvar_range)
                                  }  in
                                replace_cur
                                  (let uu___137_5951 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___137_5951.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       new_goal;
                                     FStar_Tactics_Types.opts =
                                       (uu___137_5951.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard =
                                       (uu___137_5951.FStar_Tactics_Types.is_guard)
                                   })
                            | uu____5952 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5953 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5974 = cur_goal ()  in
      bind uu____5974
        (fun goal  ->
           let uu____5985 = b  in
           match uu____5985 with
           | (bv,uu____5989) ->
               let bv' =
                 let uu____5991 =
                   let uu___138_5992 = bv  in
                   let uu____5993 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5993;
                     FStar_Syntax_Syntax.index =
                       (uu___138_5992.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___138_5992.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5991  in
               let s1 =
                 let uu____5997 =
                   let uu____5998 =
                     let uu____6005 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____6005)  in
                   FStar_Syntax_Syntax.NT uu____5998  in
                 [uu____5997]  in
               let uu____6010 = subst_goal bv bv' s1 goal  in
               (match uu____6010 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6025 = cur_goal ()  in
    bind uu____6025
      (fun goal  ->
         let uu____6034 = b  in
         match uu____6034 with
         | (bv,uu____6038) ->
             let uu____6039 =
               let uu____6048 = FStar_Tactics_Types.goal_env goal  in
               split_env bv uu____6048  in
             (match uu____6039 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____6069 = FStar_Syntax_Util.type_u ()  in
                  (match uu____6069 with
                   | (ty,u) ->
                       let uu____6078 = new_uvar "binder_retype" e0 ty  in
                       bind uu____6078
                         (fun uu____6096  ->
                            match uu____6096 with
                            | (t',u_t') ->
                                let bv'' =
                                  let uu___139_6106 = bv  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___139_6106.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___139_6106.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t'
                                  }  in
                                let s =
                                  let uu____6110 =
                                    let uu____6111 =
                                      let uu____6118 =
                                        FStar_Syntax_Syntax.bv_to_name bv''
                                         in
                                      (bv, uu____6118)  in
                                    FStar_Syntax_Syntax.NT uu____6111  in
                                  [uu____6110]  in
                                let bvs1 =
                                  FStar_List.map
                                    (fun b1  ->
                                       let uu___140_6130 = b1  in
                                       let uu____6131 =
                                         FStar_Syntax_Subst.subst s
                                           b1.FStar_Syntax_Syntax.sort
                                          in
                                       {
                                         FStar_Syntax_Syntax.ppname =
                                           (uu___140_6130.FStar_Syntax_Syntax.ppname);
                                         FStar_Syntax_Syntax.index =
                                           (uu___140_6130.FStar_Syntax_Syntax.index);
                                         FStar_Syntax_Syntax.sort =
                                           uu____6131
                                       }) bvs
                                   in
                                let env' = push_bvs e0 (bv'' :: bvs1)  in
                                bind __dismiss
                                  (fun uu____6138  ->
                                     let new_goal =
                                       let uu____6140 =
                                         FStar_Tactics_Types.goal_with_env
                                           goal env'
                                          in
                                       let uu____6141 =
                                         let uu____6142 =
                                           FStar_Tactics_Types.goal_type goal
                                            in
                                         FStar_Syntax_Subst.subst s
                                           uu____6142
                                          in
                                       FStar_Tactics_Types.goal_with_type
                                         uu____6140 uu____6141
                                        in
                                     let uu____6143 = add_goals [new_goal]
                                        in
                                     bind uu____6143
                                       (fun uu____6148  ->
                                          let uu____6149 =
                                            FStar_Syntax_Util.mk_eq2
                                              (FStar_Syntax_Syntax.U_succ u)
                                              ty bv.FStar_Syntax_Syntax.sort
                                              t'
                                             in
                                          add_irrelevant_goal
                                            "binder_retype equation" e0
                                            uu____6149
                                            goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6168 = cur_goal ()  in
      bind uu____6168
        (fun goal  ->
           let uu____6177 = b  in
           match uu____6177 with
           | (bv,uu____6181) ->
               let uu____6182 =
                 let uu____6191 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6191  in
               (match uu____6182 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____6215 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____6215
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___141_6220 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___141_6220.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___141_6220.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    let uu____6222 =
                      FStar_Tactics_Types.goal_with_env goal env'  in
                    replace_cur uu____6222))
  
let (revert : unit -> unit tac) =
  fun uu____6229  ->
    let uu____6232 = cur_goal ()  in
    bind uu____6232
      (fun goal  ->
         let uu____6238 =
           let uu____6245 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6245  in
         match uu____6238 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6261 =
                 let uu____6264 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6264  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6261
                in
             let uu____6273 = new_uvar "revert" env' typ'  in
             bind uu____6273
               (fun uu____6288  ->
                  match uu____6288 with
                  | (r,u_r) ->
                      let uu____6297 =
                        let uu____6300 =
                          let uu____6301 =
                            let uu____6302 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6302.FStar_Syntax_Syntax.pos  in
                          let uu____6305 =
                            let uu____6310 =
                              let uu____6311 =
                                let uu____6318 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6318  in
                              [uu____6311]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6310  in
                          uu____6305 FStar_Pervasives_Native.None uu____6301
                           in
                        set_solution goal uu____6300  in
                      bind uu____6297
                        (fun uu____6335  ->
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
      let uu____6347 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6347
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6360 = cur_goal ()  in
    bind uu____6360
      (fun goal  ->
         mlog
           (fun uu____6368  ->
              let uu____6369 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6370 =
                let uu____6371 =
                  let uu____6372 =
                    let uu____6379 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6379  in
                  FStar_All.pipe_right uu____6372 FStar_List.length  in
                FStar_All.pipe_right uu____6371 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6369 uu____6370)
           (fun uu____6392  ->
              let uu____6393 =
                let uu____6402 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6402  in
              match uu____6393 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6441 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6441
                        then
                          let uu____6444 =
                            let uu____6445 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6445
                             in
                          fail uu____6444
                        else check1 bvs2
                     in
                  let uu____6447 =
                    let uu____6448 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6448  in
                  if uu____6447
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6452 = check1 bvs  in
                     bind uu____6452
                       (fun uu____6458  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6460 =
                            let uu____6467 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6467  in
                          bind uu____6460
                            (fun uu____6476  ->
                               match uu____6476 with
                               | (ut,uvar_ut) ->
                                   let uu____6485 = set_solution goal ut  in
                                   bind uu____6485
                                     (fun uu____6490  ->
                                        let uu____6491 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6491))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6498  ->
    let uu____6501 = cur_goal ()  in
    bind uu____6501
      (fun goal  ->
         let uu____6507 =
           let uu____6514 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6514  in
         match uu____6507 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6522) ->
             let uu____6527 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6527)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6537 = cur_goal ()  in
    bind uu____6537
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6547 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6547  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6550  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6560 = cur_goal ()  in
    bind uu____6560
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6570 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6570  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6573  -> add_goals [g']))
  
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
            let uu____6613 = FStar_Syntax_Subst.compress t  in
            uu____6613.FStar_Syntax_Syntax.n  in
          let uu____6616 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___145_6622 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___145_6622.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___145_6622.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6616
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6638 =
                   let uu____6639 = FStar_Syntax_Subst.compress t1  in
                   uu____6639.FStar_Syntax_Syntax.n  in
                 match uu____6638 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6666 = ff hd1  in
                     bind uu____6666
                       (fun hd2  ->
                          let fa uu____6688 =
                            match uu____6688 with
                            | (a,q) ->
                                let uu____6701 = ff a  in
                                bind uu____6701 (fun a1  -> ret (a1, q))
                             in
                          let uu____6714 = mapM fa args  in
                          bind uu____6714
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6780 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6780 with
                      | (bs1,t') ->
                          let uu____6789 =
                            let uu____6792 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6792 t'  in
                          bind uu____6789
                            (fun t''  ->
                               let uu____6796 =
                                 let uu____6797 =
                                   let uu____6814 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6821 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6814, uu____6821, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6797  in
                               ret uu____6796))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6890 = ff hd1  in
                     bind uu____6890
                       (fun hd2  ->
                          let ffb br =
                            let uu____6905 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6905 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6937 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6937  in
                                let uu____6938 = ff1 e  in
                                bind uu____6938
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6953 = mapM ffb brs  in
                          bind uu____6953
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6997;
                          FStar_Syntax_Syntax.lbtyp = uu____6998;
                          FStar_Syntax_Syntax.lbeff = uu____6999;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7001;
                          FStar_Syntax_Syntax.lbpos = uu____7002;_}::[]),e)
                     ->
                     let lb =
                       let uu____7027 =
                         let uu____7028 = FStar_Syntax_Subst.compress t1  in
                         uu____7028.FStar_Syntax_Syntax.n  in
                       match uu____7027 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7032) -> lb
                       | uu____7045 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7054 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7054
                         (fun def1  ->
                            ret
                              (let uu___142_7060 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___142_7060.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___142_7060.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___142_7060.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___142_7060.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___142_7060.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___142_7060.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7061 = fflb lb  in
                     bind uu____7061
                       (fun lb1  ->
                          let uu____7071 =
                            let uu____7076 =
                              let uu____7077 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7077]  in
                            FStar_Syntax_Subst.open_term uu____7076 e  in
                          match uu____7071 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7101 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7101  in
                              let uu____7102 = ff1 e1  in
                              bind uu____7102
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7143 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7143
                         (fun def  ->
                            ret
                              (let uu___143_7149 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___143_7149.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___143_7149.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___143_7149.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___143_7149.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___143_7149.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___143_7149.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7150 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7150 with
                      | (lbs1,e1) ->
                          let uu____7165 = mapM fflb lbs1  in
                          bind uu____7165
                            (fun lbs2  ->
                               let uu____7177 = ff e1  in
                               bind uu____7177
                                 (fun e2  ->
                                    let uu____7185 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7185 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7253 = ff t2  in
                     bind uu____7253
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7284 = ff t2  in
                     bind uu____7284
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7291 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___144_7298 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___144_7298.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___144_7298.FStar_Syntax_Syntax.vars)
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
            let uu____7335 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7335 with
            | (t1,lcomp,g) ->
                let uu____7347 =
                  (let uu____7350 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7350) ||
                    (let uu____7352 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7352)
                   in
                if uu____7347
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7362 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7362
                       (fun uu____7378  ->
                          match uu____7378 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7391  ->
                                    let uu____7392 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7393 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7392 uu____7393);
                               (let uu____7394 =
                                  let uu____7397 =
                                    let uu____7398 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7398 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7397
                                    opts
                                   in
                                bind uu____7394
                                  (fun uu____7401  ->
                                     let uu____7402 =
                                       bind tau
                                         (fun uu____7408  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7414  ->
                                                 let uu____7415 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7416 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7415 uu____7416);
                                            ret ut1)
                                        in
                                     focus uu____7402))))
                      in
                   let uu____7417 = trytac' rewrite_eq  in
                   bind uu____7417
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
          let uu____7615 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7615
            (fun t1  ->
               let uu____7623 =
                 f env
                   (let uu___148_7632 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___148_7632.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___148_7632.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7623
                 (fun uu____7648  ->
                    match uu____7648 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7671 =
                               let uu____7672 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7672.FStar_Syntax_Syntax.n  in
                             match uu____7671 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7705 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7705
                                   (fun uu____7730  ->
                                      match uu____7730 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7746 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7746
                                            (fun uu____7773  ->
                                               match uu____7773 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___146_7803 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___146_7803.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___146_7803.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7839 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7839 with
                                  | (bs1,t') ->
                                      let uu____7854 =
                                        let uu____7861 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7861 ctrl1 t'
                                         in
                                      bind uu____7854
                                        (fun uu____7879  ->
                                           match uu____7879 with
                                           | (t'',ctrl2) ->
                                               let uu____7894 =
                                                 let uu____7901 =
                                                   let uu___147_7904 = t4  in
                                                   let uu____7907 =
                                                     let uu____7908 =
                                                       let uu____7925 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7932 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7925,
                                                         uu____7932, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7908
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7907;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___147_7904.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___147_7904.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7901, ctrl2)  in
                                               ret uu____7894))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7979 -> ret (t3, ctrl1))))

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
              let uu____8022 = ctrl_tac_fold f env ctrl t  in
              bind uu____8022
                (fun uu____8046  ->
                   match uu____8046 with
                   | (t1,ctrl1) ->
                       let uu____8061 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8061
                         (fun uu____8088  ->
                            match uu____8088 with
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
              let uu____8170 =
                let uu____8177 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8177
                  (fun uu____8186  ->
                     let uu____8187 = ctrl t1  in
                     bind uu____8187
                       (fun res  ->
                          let uu____8210 = trivial ()  in
                          bind uu____8210 (fun uu____8218  -> ret res)))
                 in
              bind uu____8170
                (fun uu____8234  ->
                   match uu____8234 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8258 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8258 with
                          | (t2,lcomp,g) ->
                              let uu____8274 =
                                (let uu____8277 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8277) ||
                                  (let uu____8279 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8279)
                                 in
                              if uu____8274
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8294 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8294
                                   (fun uu____8314  ->
                                      match uu____8314 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8331  ->
                                                let uu____8332 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8333 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8332 uu____8333);
                                           (let uu____8334 =
                                              let uu____8337 =
                                                let uu____8338 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8338 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8337 opts
                                               in
                                            bind uu____8334
                                              (fun uu____8345  ->
                                                 let uu____8346 =
                                                   bind rewriter
                                                     (fun uu____8360  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8366  ->
                                                             let uu____8367 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8368 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8367
                                                               uu____8368);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8346)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____8416 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8416 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8453  ->
                     let uu____8454 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____8454);
                bind dismiss_all
                  (fun uu____8457  ->
                     let uu____8458 =
                       let uu____8465 = FStar_Tactics_Types.goal_env g  in
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts) uu____8465 keepGoing
                         gt1
                        in
                     bind uu____8458
                       (fun uu____8477  ->
                          match uu____8477 with
                          | (gt',uu____8485) ->
                              (log ps
                                 (fun uu____8489  ->
                                    let uu____8490 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____8490);
                               (let uu____8491 = push_goals gs  in
                                bind uu____8491
                                  (fun uu____8496  ->
                                     let uu____8497 =
                                       let uu____8500 =
                                         FStar_Tactics_Types.goal_with_type g
                                           gt'
                                          in
                                       [uu____8500]  in
                                     add_goals uu____8497)))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____8526 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____8526 with
           | (g,gs) ->
               let gt1 = FStar_Tactics_Types.goal_type g  in
               (log ps
                  (fun uu____8563  ->
                     let uu____8564 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____8564);
                bind dismiss_all
                  (fun uu____8567  ->
                     let uu____8568 =
                       let uu____8571 = FStar_Tactics_Types.goal_env g  in
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         uu____8571 gt1
                        in
                     bind uu____8568
                       (fun gt'  ->
                          log ps
                            (fun uu____8579  ->
                               let uu____8580 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____8580);
                          (let uu____8581 = push_goals gs  in
                           bind uu____8581
                             (fun uu____8586  ->
                                let uu____8587 =
                                  let uu____8590 =
                                    FStar_Tactics_Types.goal_with_type g gt'
                                     in
                                  [uu____8590]  in
                                add_goals uu____8587))))))
  
let (trefl : unit -> unit tac) =
  fun uu____8597  ->
    let uu____8600 = cur_goal ()  in
    bind uu____8600
      (fun g  ->
         let uu____8618 =
           let uu____8623 = FStar_Tactics_Types.goal_type g  in
           FStar_Syntax_Util.un_squash uu____8623  in
         match uu____8618 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8631 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8631 with
              | (hd1,args) ->
                  let uu____8664 =
                    let uu____8675 =
                      let uu____8676 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8676.FStar_Syntax_Syntax.n  in
                    (uu____8675, args)  in
                  (match uu____8664 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8688::(l,uu____8690)::(r,uu____8692)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8719 =
                         let uu____8722 = FStar_Tactics_Types.goal_env g  in
                         do_unify uu____8722 l r  in
                       bind uu____8719
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8729 =
                                let uu____8730 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8730 l  in
                              let uu____8731 =
                                let uu____8732 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____8732 r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8729 uu____8731
                            else solve' g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8735) ->
                       let uu____8748 =
                         let uu____8749 = FStar_Tactics_Types.goal_env g  in
                         tts uu____8749 t  in
                       fail1 "trefl: not an equality (%s)" uu____8748))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8758  ->
    let uu____8761 = cur_goal ()  in
    bind uu____8761
      (fun g  ->
         let uu____8767 =
           let uu____8774 = FStar_Tactics_Types.goal_env g  in
           let uu____8775 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8774 uu____8775  in
         bind uu____8767
           (fun uu____8784  ->
              match uu____8784 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___149_8794 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___149_8794.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___149_8794.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___149_8794.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8797  ->
                       let uu____8798 =
                         let uu____8801 = FStar_Tactics_Types.goal_env g  in
                         let uu____8802 =
                           let uu____8803 =
                             let uu____8804 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8805 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8804
                               uu____8805
                              in
                           let uu____8806 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8807 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8803 uu____8806 u
                             uu____8807
                            in
                         add_irrelevant_goal "dup equation" uu____8801
                           uu____8802 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8798
                         (fun uu____8810  ->
                            let uu____8811 = add_goals [g']  in
                            bind uu____8811 (fun uu____8815  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8822  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___150_8839 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___150_8839.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___150_8839.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___150_8839.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___150_8839.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___150_8839.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___150_8839.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___150_8839.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___150_8839.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___150_8839.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___150_8839.FStar_Tactics_Types.freshness)
                })
         | uu____8840 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8849  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___151_8862 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___151_8862.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___151_8862.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___151_8862.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___151_8862.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___151_8862.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___151_8862.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___151_8862.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___151_8862.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___151_8862.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___151_8862.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8869  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8876 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8896 =
      let uu____8903 = cur_goal ()  in
      bind uu____8903
        (fun g  ->
           let uu____8913 =
             let uu____8922 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8922 t  in
           bind uu____8913
             (fun uu____8950  ->
                match uu____8950 with
                | (t1,typ,guard) ->
                    let uu____8966 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8966 with
                     | (hd1,args) ->
                         let uu____9009 =
                           let uu____9022 =
                             let uu____9023 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9023.FStar_Syntax_Syntax.n  in
                           (uu____9022, args)  in
                         (match uu____9009 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9042)::(q,uu____9044)::[]) when
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
                                let uu____9082 =
                                  let uu____9083 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9083
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9082
                                 in
                              let g2 =
                                let uu____9085 =
                                  let uu____9086 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9086
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9085
                                 in
                              bind __dismiss
                                (fun uu____9093  ->
                                   let uu____9094 = add_goals [g1; g2]  in
                                   bind uu____9094
                                     (fun uu____9103  ->
                                        let uu____9104 =
                                          let uu____9109 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9110 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9109, uu____9110)  in
                                        ret uu____9104))
                          | uu____9115 ->
                              let uu____9128 =
                                let uu____9129 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9129 typ  in
                              fail1 "Not a disjunction: %s" uu____9128))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8896
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9159 = cur_goal ()  in
    bind uu____9159
      (fun g  ->
         FStar_Options.push ();
         (let uu____9172 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____9172);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___152_9179 = g  in
                 {
                   FStar_Tactics_Types.goal_main_env =
                     (uu___152_9179.FStar_Tactics_Types.goal_main_env);
                   FStar_Tactics_Types.goal_ctx_uvar =
                     (uu___152_9179.FStar_Tactics_Types.goal_ctx_uvar);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___152_9179.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____9187  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9200  ->
    let uu____9203 = cur_goal ()  in
    bind uu____9203
      (fun g  ->
         let uu____9209 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9209)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9218  ->
    let uu____9221 = cur_goal ()  in
    bind uu____9221
      (fun g  ->
         let uu____9227 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9227)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9236  ->
    let uu____9239 = cur_goal ()  in
    bind uu____9239
      (fun g  ->
         let uu____9245 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9245)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9262 =
        let uu____9265 = cur_goal ()  in
        bind uu____9265
          (fun goal  ->
             let env =
               let uu____9273 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9273 ty  in
             let uu____9274 = __tc env tm  in
             bind uu____9274
               (fun uu____9294  ->
                  match uu____9294 with
                  | (tm1,typ,guard) ->
                      let uu____9306 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9306 (fun uu____9310  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9262
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9333 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9339 =
              let uu____9346 =
                let uu____9347 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9347
                 in
              new_uvar "uvar_env.2" env uu____9346  in
            bind uu____9339
              (fun uu____9363  ->
                 match uu____9363 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9333
        (fun typ  ->
           let uu____9375 = new_uvar "uvar_env" env typ  in
           bind uu____9375
             (fun uu____9389  -> match uu____9389 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9407 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9426 -> g.FStar_Tactics_Types.opts
             | uu____9429 -> FStar_Options.peek ()  in
           let uu____9432 = FStar_Syntax_Util.head_and_args t  in
           match uu____9432 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9450);
                FStar_Syntax_Syntax.pos = uu____9451;
                FStar_Syntax_Syntax.vars = uu____9452;_},uu____9453)
               ->
               let env1 =
                 let uu___153_9495 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___153_9495.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___153_9495.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___153_9495.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___153_9495.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___153_9495.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___153_9495.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___153_9495.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___153_9495.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___153_9495.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___153_9495.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___153_9495.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___153_9495.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___153_9495.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___153_9495.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___153_9495.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___153_9495.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___153_9495.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___153_9495.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___153_9495.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___153_9495.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___153_9495.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___153_9495.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___153_9495.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___153_9495.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___153_9495.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___153_9495.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___153_9495.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___153_9495.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___153_9495.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___153_9495.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___153_9495.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___153_9495.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___153_9495.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___153_9495.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___153_9495.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___153_9495.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___153_9495.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let g1 =
                 let uu____9498 =
                   bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                 FStar_Tactics_Types.goal_with_type g uu____9498  in
               add_goals [g1]
           | uu____9499 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9407
  
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
          (fun uu____9560  ->
             let uu____9561 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9561
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
        (fun uu____9582  ->
           let uu____9583 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9583)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9593 =
      mlog
        (fun uu____9598  ->
           let uu____9599 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9599)
        (fun uu____9602  ->
           let uu____9603 = cur_goal ()  in
           bind uu____9603
             (fun g  ->
                let uu____9609 =
                  let uu____9618 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9618 ty  in
                bind uu____9609
                  (fun uu____9630  ->
                     match uu____9630 with
                     | (ty1,uu____9640,guard) ->
                         let uu____9642 =
                           let uu____9645 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9645 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9642
                           (fun uu____9648  ->
                              let uu____9649 =
                                let uu____9652 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9653 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9652 uu____9653 ty1  in
                              bind uu____9649
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9659 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9659
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
                                        let uu____9665 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9666 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9665 uu____9666
                                         in
                                      let nty =
                                        let uu____9668 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9668 ty1  in
                                      let uu____9669 =
                                        let uu____9672 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9672 ng nty  in
                                      bind uu____9669
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9678 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9678
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9593
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9700::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9728 = init xs  in x :: uu____9728
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9745) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9802 = last args  in
        (match uu____9802 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9824 =
               let uu____9825 =
                 let uu____9830 =
                   let uu____9831 =
                     let uu____9836 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9836  in
                   uu____9831 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9830, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9825  in
             FStar_All.pipe_left ret uu____9824)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9847,uu____9848) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9892 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9892 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9925 =
                    let uu____9926 =
                      let uu____9931 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9931)  in
                    FStar_Reflection_Data.Tv_Abs uu____9926  in
                  FStar_All.pipe_left ret uu____9925))
    | FStar_Syntax_Syntax.Tm_type uu____9934 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9954 ->
        let uu____9967 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9967 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9997 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9997 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____10036 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____10044 =
          let uu____10045 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____10045  in
        FStar_All.pipe_left ret uu____10044
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u,([],uu____10049)) ->
        let uu____10070 =
          let uu____10071 =
            let uu____10080 =
              let uu____10081 =
                FStar_Syntax_Unionfind.uvar_id
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              FStar_BigInt.of_int_fs uu____10081  in
            (uu____10080, (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders),
              (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ))
             in
          FStar_Reflection_Data.Tv_Uvar uu____10071  in
        FStar_All.pipe_left ret uu____10070
    | FStar_Syntax_Syntax.Tm_uvar uu____10084 ->
        failwith "NOT FULLY SUPPORTED"
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____10124 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____10129 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____10129 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____10168 ->
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
           | FStar_Util.Inr uu____10198 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____10202 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____10202 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____10222 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____10226 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____10280 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____10280
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____10299 =
                let uu____10306 =
                  FStar_List.map
                    (fun uu____10318  ->
                       match uu____10318 with
                       | (p1,uu____10326) -> inspect_pat p1) ps
                   in
                (fv, uu____10306)  in
              FStar_Reflection_Data.Pat_Cons uu____10299
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
            (fun uu___96_10410  ->
               match uu___96_10410 with
               | (pat,uu____10428,t4) ->
                   let uu____10442 = inspect_pat pat  in (uu____10442, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____10449 ->
        ((let uu____10451 =
            let uu____10456 =
              let uu____10457 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____10458 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____10457
                uu____10458
               in
            (FStar_Errors.Warning_CantInspect, uu____10456)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10451);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10471 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10471
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10475 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10475
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10479 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10479
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10486 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10486
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10509 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10509
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10526 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10526
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10545 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10545
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10553 =
          let uu____10556 =
            let uu____10563 =
              let uu____10564 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10564  in
            FStar_Syntax_Syntax.mk uu____10563  in
          uu____10556 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10553
    | FStar_Reflection_Data.Tv_Uvar (u,g,bs,t) ->
        let uu____10576 =
          let uu____10579 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____10579 (g, bs, t)  in
        FStar_All.pipe_left ret uu____10576
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10600 =
          let uu____10603 =
            let uu____10610 =
              let uu____10611 =
                let uu____10624 =
                  let uu____10627 =
                    let uu____10628 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10628]  in
                  FStar_Syntax_Subst.close uu____10627 t2  in
                ((false, [lb]), uu____10624)  in
              FStar_Syntax_Syntax.Tm_let uu____10611  in
            FStar_Syntax_Syntax.mk uu____10610  in
          uu____10603 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10600
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10664 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10664 with
         | (lbs,body) ->
             let uu____10679 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10679)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10717 =
                let uu____10718 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10718  in
              FStar_All.pipe_left wrap uu____10717
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10725 =
                let uu____10726 =
                  let uu____10739 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10755 = pack_pat p1  in
                         (uu____10755, false)) ps
                     in
                  (fv, uu____10739)  in
                FStar_Syntax_Syntax.Pat_cons uu____10726  in
              FStar_All.pipe_left wrap uu____10725
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
            (fun uu___97_10801  ->
               match uu___97_10801 with
               | (pat,t1) ->
                   let uu____10818 = pack_pat pat  in
                   (uu____10818, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10866 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10866
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10898 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10898
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10948 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10948
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10991 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10991
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11012 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11012 with
      | (u,ctx_uvars,g_u) ->
          let uu____11044 = FStar_List.hd ctx_uvars  in
          (match uu____11044 with
           | (ctx_uvar,uu____11058) ->
               let g =
                 let uu____11060 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11060 false
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
      let uu____11075 = goal_of_goal_ty env typ  in
      match uu____11075 with
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
          let uu____11091 = FStar_Tactics_Types.goal_witness g  in
          (ps, uu____11091)
  