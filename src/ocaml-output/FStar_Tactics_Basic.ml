open Prims
type goal = FStar_Tactics_Types.goal
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
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
let run_safe :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  =
  fun t  ->
    fun p  ->
      try t.tac_f p
      with
      | e ->
          let uu____168 =
            let uu____173 = FStar_Util.message_of_exn e  in (uu____173, p)
             in
          FStar_Tactics_Result.Failed uu____168
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____229 = run t1 p  in
           match uu____229 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____236 = t2 a  in run uu____236 q
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
    let uu____256 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____256 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____274 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____275 =
      let uu____276 = check_goal_solved g  in
      match uu____276 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____280 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____280
       in
    FStar_Util.format2 "%s%s" uu____274 uu____275
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____296 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____296
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____312 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____312
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____333 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____333
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____340) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____350) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____365 =
      let uu____370 =
        let uu____371 = FStar_Tactics_Types.goal_env g  in
        let uu____372 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____371 uu____372  in
      FStar_Syntax_Util.un_squash uu____370  in
    match uu____365 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____378 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____406 =
            let uu____407 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____407  in
          if uu____406 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____415 . 'Auu____415 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____427 = goal_to_string goal  in tacprint uu____427
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____439 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____443 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____443))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____452  ->
    match uu____452 with
    | (msg,ps) ->
        let uu____459 =
          let uu____462 =
            let uu____463 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____463 msg
             in
          let uu____464 =
            let uu____467 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____468 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____468
              else ""  in
            let uu____470 =
              let uu____473 =
                let uu____474 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____475 =
                  let uu____476 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____476  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____474
                  uu____475
                 in
              let uu____479 =
                let uu____482 =
                  let uu____483 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____484 =
                    let uu____485 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____485  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____483
                    uu____484
                   in
                [uu____482]  in
              uu____473 :: uu____479  in
            uu____467 :: uu____470  in
          uu____462 :: uu____464  in
        FStar_String.concat "" uu____459
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____494 =
        let uu____495 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____495  in
      let uu____496 =
        let uu____501 =
          let uu____502 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____502  in
        FStar_Syntax_Print.binders_to_json uu____501  in
      FStar_All.pipe_right uu____494 uu____496  in
    let uu____503 =
      let uu____510 =
        let uu____517 =
          let uu____522 =
            let uu____523 =
              let uu____530 =
                let uu____535 =
                  let uu____536 =
                    let uu____537 = FStar_Tactics_Types.goal_env g  in
                    let uu____538 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____537 uu____538  in
                  FStar_Util.JsonStr uu____536  in
                ("witness", uu____535)  in
              let uu____539 =
                let uu____546 =
                  let uu____551 =
                    let uu____552 =
                      let uu____553 = FStar_Tactics_Types.goal_env g  in
                      let uu____554 = FStar_Tactics_Types.goal_type g  in
                      tts uu____553 uu____554  in
                    FStar_Util.JsonStr uu____552  in
                  ("type", uu____551)  in
                [uu____546]  in
              uu____530 :: uu____539  in
            FStar_Util.JsonAssoc uu____523  in
          ("goal", uu____522)  in
        [uu____517]  in
      ("hyps", g_binders) :: uu____510  in
    FStar_Util.JsonAssoc uu____503
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____587  ->
    match uu____587 with
    | (msg,ps) ->
        let uu____594 =
          let uu____601 =
            let uu____608 =
              let uu____615 =
                let uu____622 =
                  let uu____627 =
                    let uu____628 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____628  in
                  ("goals", uu____627)  in
                let uu____631 =
                  let uu____638 =
                    let uu____643 =
                      let uu____644 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____644  in
                    ("smt-goals", uu____643)  in
                  [uu____638]  in
                uu____622 :: uu____631  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____615
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____608  in
          let uu____667 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____680 =
                let uu____685 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____685)  in
              [uu____680]
            else []  in
          FStar_List.append uu____601 uu____667  in
        FStar_Util.JsonAssoc uu____594
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____715  ->
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
         (let uu____738 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____738 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____756 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____756 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____789 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____789 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____820 =
              let uu____823 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____823  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____820);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____904 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____904
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____912 . Prims.string -> Prims.string -> 'Auu____912 tac =
  fun msg  ->
    fun x  -> let uu____925 = FStar_Util.format1 msg x  in fail uu____925
  
let fail2 :
  'Auu____934 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____934 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____952 = FStar_Util.format2 msg x y  in fail uu____952
  
let fail3 :
  'Auu____963 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____963 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____986 = FStar_Util.format3 msg x y z  in fail uu____986
  
let fail4 :
  'Auu____999 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____999 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1027 = FStar_Util.format4 msg x y z w  in
            fail uu____1027
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1060 = run t ps  in
         match uu____1060 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___96_1084 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___96_1084.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___96_1084.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___96_1084.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___96_1084.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___96_1084.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___96_1084.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___96_1084.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___96_1084.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___96_1084.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___96_1084.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1111 = trytac' t  in
    bind uu____1111
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1138 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1174 = trytac t  in run uu____1174 ps
         with
         | FStar_Errors.Err (uu____1190,msg) ->
             (log ps
                (fun uu____1194  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1199,msg,uu____1201) ->
             (log ps
                (fun uu____1204  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1237 = run t ps  in
           match uu____1237 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1256  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1277 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1277
         then
           let uu____1278 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1279 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1278
             uu____1279
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1291 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1291
            then
              let uu____1292 = FStar_Util.string_of_bool res  in
              let uu____1293 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1294 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1292 uu____1293 uu____1294
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1302,msg) ->
             mlog
               (fun uu____1305  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1307  -> ret false)
         | FStar_Errors.Error (uu____1308,msg,r) ->
             mlog
               (fun uu____1313  ->
                  let uu____1314 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1314) (fun uu____1316  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1339  ->
             (let uu____1341 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1341
              then
                (FStar_Options.push ();
                 (let uu____1343 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1345 =
                let uu____1348 = __do_unify env t1 t2  in
                bind uu____1348
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
              bind uu____1345
                (fun r  ->
                   (let uu____1364 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1364 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___101_1372 = ps  in
         let uu____1373 =
           FStar_List.filter
             (fun g  ->
                let uu____1379 = check_goal_solved g  in
                FStar_Option.isNone uu____1379) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___101_1372.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___101_1372.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___101_1372.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1373;
           FStar_Tactics_Types.smt_goals =
             (uu___101_1372.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___101_1372.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___101_1372.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___101_1372.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___101_1372.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___101_1372.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___101_1372.FStar_Tactics_Types.freshness)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1396 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1396 with
      | FStar_Pervasives_Native.Some uu____1401 ->
          let uu____1402 =
            let uu____1403 = goal_to_string goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1403  in
          fail uu____1402
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1419 = FStar_Tactics_Types.goal_env goal  in
      let uu____1420 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1419 solution uu____1420
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1426 =
         let uu___102_1427 = p  in
         let uu____1428 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___102_1427.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___102_1427.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___102_1427.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1428;
           FStar_Tactics_Types.smt_goals =
             (uu___102_1427.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___102_1427.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___102_1427.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___102_1427.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___102_1427.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___102_1427.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___102_1427.FStar_Tactics_Types.freshness)
         }  in
       set uu____1426)
  
let (dismiss : unit -> unit tac) =
  fun uu____1437  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1444 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1465  ->
           let uu____1466 =
             let uu____1467 = FStar_Tactics_Types.goal_witness goal  in
             tts e uu____1467  in
           let uu____1468 = tts e solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1466 uu____1468)
        (fun uu____1471  ->
           let uu____1472 = trysolve goal solution  in
           bind uu____1472
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1480  -> remove_solved_goals)
                else
                  (let uu____1482 =
                     let uu____1483 =
                       let uu____1484 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1484 solution  in
                     let uu____1485 =
                       let uu____1486 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1487 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1486 uu____1487  in
                     let uu____1488 =
                       let uu____1489 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1490 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1489 uu____1490  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1483 uu____1485 uu____1488
                      in
                   fail uu____1482)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1505 = set_solution goal solution  in
      bind uu____1505
        (fun uu____1509  ->
           bind __dismiss (fun uu____1511  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___103_1518 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___103_1518.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___103_1518.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___103_1518.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___103_1518.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___103_1518.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___103_1518.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___103_1518.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___103_1518.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___103_1518.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___103_1518.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1537 = FStar_Options.defensive ()  in
    if uu____1537
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1542 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1542)
         in
      let b2 =
        b1 &&
          (let uu____1545 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1545)
         in
      let rec aux b3 e =
        let uu____1557 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1557 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1575 =
        (let uu____1578 = aux b2 env  in Prims.op_Negation uu____1578) &&
          (let uu____1580 = FStar_ST.op_Bang nwarn  in
           uu____1580 < (Prims.parse_int "5"))
         in
      (if uu____1575
       then
         ((let uu____1605 =
             let uu____1606 = FStar_Tactics_Types.goal_type g  in
             uu____1606.FStar_Syntax_Syntax.pos  in
           let uu____1609 =
             let uu____1614 =
               let uu____1615 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1615
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1614)  in
           FStar_Errors.log_issue uu____1605 uu____1609);
          (let uu____1616 =
             let uu____1617 = FStar_ST.op_Bang nwarn  in
             uu____1617 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1616))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___104_1685 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_1685.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_1685.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___104_1685.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_1685.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_1685.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_1685.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_1685.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_1685.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___104_1685.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___104_1685.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___105_1705 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___105_1705.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___105_1705.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___105_1705.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___105_1705.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___105_1705.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___105_1705.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___105_1705.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___105_1705.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___105_1705.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___105_1705.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___106_1725 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___106_1725.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___106_1725.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___106_1725.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___106_1725.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___106_1725.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___106_1725.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___106_1725.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___106_1725.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___106_1725.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___106_1725.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___107_1745 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___107_1745.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___107_1745.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___107_1745.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___107_1745.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___107_1745.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___107_1745.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___107_1745.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___107_1745.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___107_1745.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___107_1745.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1756  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___108_1770 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_1770.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_1770.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___108_1770.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___108_1770.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_1770.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_1770.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_1770.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_1770.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___108_1770.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___108_1770.FStar_Tactics_Types.freshness)
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
        let uu____1806 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1806 with
        | (u,ctx_uvar,g_u) ->
            let uu____1840 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1840
              (fun uu____1849  ->
                 let uu____1850 =
                   let uu____1855 =
                     let uu____1856 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1856  in
                   (u, uu____1855)  in
                 ret uu____1850)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1874 = FStar_Syntax_Util.un_squash t  in
    match uu____1874 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1884 =
          let uu____1885 = FStar_Syntax_Subst.compress t'  in
          uu____1885.FStar_Syntax_Syntax.n  in
        (match uu____1884 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1889 -> false)
    | uu____1890 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1900 = FStar_Syntax_Util.un_squash t  in
    match uu____1900 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1910 =
          let uu____1911 = FStar_Syntax_Subst.compress t'  in
          uu____1911.FStar_Syntax_Syntax.n  in
        (match uu____1910 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1915 -> false)
    | uu____1916 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1927  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1938 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1938 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1945 = goal_to_string hd1  in
                    let uu____1946 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1945 uu____1946);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1953  ->
    let uu____1956 =
      let uu____1959 = cur_goal ()  in
      bind uu____1959
        (fun g  ->
           (let uu____1966 =
              let uu____1967 = FStar_Tactics_Types.goal_type g  in
              uu____1967.FStar_Syntax_Syntax.pos  in
            let uu____1970 =
              let uu____1975 =
                let uu____1976 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1976
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1975)  in
            FStar_Errors.log_issue uu____1966 uu____1970);
           solve' g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1956
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1987  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___109_1997 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___109_1997.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___109_1997.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___109_1997.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___109_1997.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___109_1997.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___109_1997.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___109_1997.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___109_1997.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___109_1997.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___109_1997.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1998 = set ps1  in
         bind uu____1998
           (fun uu____2003  ->
              let uu____2004 = FStar_BigInt.of_int_fs n1  in ret uu____2004))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____2011  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____2019 = FStar_BigInt.of_int_fs n1  in ret uu____2019)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____2032  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____2040 = FStar_BigInt.of_int_fs n1  in ret uu____2040)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____2053  ->
    let uu____2056 = cur_goal ()  in
    bind uu____2056 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2088 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2088 phi  in
          let uu____2089 = new_uvar reason env typ  in
          bind uu____2089
            (fun uu____2104  ->
               match uu____2104 with
               | (uu____2111,ctx_uvar) ->
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
             (fun uu____2156  ->
                let uu____2157 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2157)
             (fun uu____2160  ->
                let e1 =
                  let uu___110_2162 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___110_2162.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___110_2162.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___110_2162.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___110_2162.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___110_2162.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___110_2162.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___110_2162.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___110_2162.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___110_2162.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___110_2162.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___110_2162.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___110_2162.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___110_2162.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___110_2162.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___110_2162.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___110_2162.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___110_2162.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___110_2162.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___110_2162.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___110_2162.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___110_2162.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___110_2162.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___110_2162.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___110_2162.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___110_2162.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___110_2162.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___110_2162.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___110_2162.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___110_2162.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___110_2162.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___110_2162.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___110_2162.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___110_2162.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___110_2162.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___110_2162.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___110_2162.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___110_2162.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___110_2162.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2182 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2182
                with
                | FStar_Errors.Err (uu____2209,msg) ->
                    let uu____2211 = tts e1 t  in
                    let uu____2212 =
                      let uu____2213 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2213
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2211 uu____2212 msg
                | FStar_Errors.Error (uu____2220,msg,uu____2222) ->
                    let uu____2223 = tts e1 t  in
                    let uu____2224 =
                      let uu____2225 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2225
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2223 uu____2224 msg))
  
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
  fun uu____2252  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___113_2270 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___113_2270.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___113_2270.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___113_2270.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___113_2270.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___113_2270.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___113_2270.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___113_2270.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___113_2270.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___113_2270.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___113_2270.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2294 = get_guard_policy ()  in
      bind uu____2294
        (fun old_pol  ->
           let uu____2300 = set_guard_policy pol  in
           bind uu____2300
             (fun uu____2304  ->
                bind t
                  (fun r  ->
                     let uu____2308 = set_guard_policy old_pol  in
                     bind uu____2308 (fun uu____2312  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2337 =
            let uu____2338 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2338.FStar_TypeChecker_Env.guard_f  in
          match uu____2337 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2342 = istrivial e f  in
              if uu____2342
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2350 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2350
                           (fun goal  ->
                              let goal1 =
                                let uu___114_2357 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___114_2357.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___114_2357.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___114_2357.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2358 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2358
                           (fun goal  ->
                              let goal1 =
                                let uu___115_2365 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___115_2365.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___115_2365.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___115_2365.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2373 =
                              let uu____2374 =
                                let uu____2375 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2375
                                 in
                              Prims.op_Negation uu____2374  in
                            if uu____2373
                            then
                              mlog
                                (fun uu____2380  ->
                                   let uu____2381 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2381)
                                (fun uu____2383  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2390 ->
                              mlog
                                (fun uu____2393  ->
                                   let uu____2394 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2394)
                                (fun uu____2396  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2406 =
      let uu____2409 = cur_goal ()  in
      bind uu____2409
        (fun goal  ->
           let uu____2415 =
             let uu____2424 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2424 t  in
           bind uu____2415
             (fun uu____2436  ->
                match uu____2436 with
                | (t1,typ,guard) ->
                    let uu____2448 =
                      let uu____2451 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2451 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2448 (fun uu____2453  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2406
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2482 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2482 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2493  ->
    let uu____2496 = cur_goal ()  in
    bind uu____2496
      (fun goal  ->
         let uu____2502 =
           let uu____2503 = FStar_Tactics_Types.goal_env goal  in
           let uu____2504 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2503 uu____2504  in
         if uu____2502
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2508 =
              let uu____2509 = FStar_Tactics_Types.goal_env goal  in
              let uu____2510 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2509 uu____2510  in
            fail1 "Not a trivial goal: %s" uu____2508))
  
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
          let uu____2539 =
            let uu____2540 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2540.FStar_TypeChecker_Env.guard_f  in
          match uu____2539 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2548 = istrivial e f  in
              if uu____2548
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2556 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2556
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___118_2566 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___118_2566.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___118_2566.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___118_2566.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2573  ->
    let uu____2576 = cur_goal ()  in
    bind uu____2576
      (fun g  ->
         let uu____2582 = is_irrelevant g  in
         if uu____2582
         then bind __dismiss (fun uu____2586  -> add_smt_goals [g])
         else
           (let uu____2588 =
              let uu____2589 = FStar_Tactics_Types.goal_env g  in
              let uu____2590 = FStar_Tactics_Types.goal_type g  in
              tts uu____2589 uu____2590  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2588))
  
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
             let uu____2639 =
               try
                 let uu____2673 =
                   let uu____2682 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2682 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2673
               with | uu____2704 -> fail "divide: not enough goals"  in
             bind uu____2639
               (fun uu____2731  ->
                  match uu____2731 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___119_2757 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___119_2757.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___119_2757.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___119_2757.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___119_2757.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___119_2757.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___119_2757.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___119_2757.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___119_2757.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___119_2757.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___120_2759 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___120_2759.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___120_2759.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___120_2759.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___120_2759.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___120_2759.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___120_2759.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___120_2759.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___120_2759.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___120_2759.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2760 = set lp  in
                      bind uu____2760
                        (fun uu____2768  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2782 = set rp  in
                                     bind uu____2782
                                       (fun uu____2790  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___121_2806 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___121_2806.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___121_2806.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2807 = set p'
                                                       in
                                                    bind uu____2807
                                                      (fun uu____2815  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2821 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2842 = divide FStar_BigInt.one f idtac  in
    bind uu____2842
      (fun uu____2855  -> match uu____2855 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2892::uu____2893 ->
             let uu____2896 =
               let uu____2905 = map tau  in
               divide FStar_BigInt.one tau uu____2905  in
             bind uu____2896
               (fun uu____2923  ->
                  match uu____2923 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2964 =
        bind t1
          (fun uu____2969  ->
             let uu____2970 = map t2  in
             bind uu____2970 (fun uu____2978  -> ret ()))
         in
      focus uu____2964
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2987  ->
    let uu____2990 =
      let uu____2993 = cur_goal ()  in
      bind uu____2993
        (fun goal  ->
           let uu____3002 =
             let uu____3009 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3009  in
           match uu____3002 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3018 =
                 let uu____3019 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3019  in
               if uu____3018
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3024 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3024 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3034 = new_uvar "intro" env' typ'  in
                  bind uu____3034
                    (fun uu____3050  ->
                       match uu____3050 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3070 = set_solution goal sol  in
                           bind uu____3070
                             (fun uu____3076  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3078 =
                                  let uu____3081 = bnorm_goal g  in
                                  replace_cur uu____3081  in
                                bind uu____3078 (fun uu____3083  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3088 =
                 let uu____3089 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3090 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3089 uu____3090  in
               fail1 "goal is not an arrow (%s)" uu____3088)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2990
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3105  ->
    let uu____3112 = cur_goal ()  in
    bind uu____3112
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3129 =
            let uu____3136 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3136  in
          match uu____3129 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3149 =
                let uu____3150 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3150  in
              if uu____3149
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3163 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3163
                    in
                 let bs =
                   let uu____3171 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3171; b]  in
                 let env' =
                   let uu____3189 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3189 bs  in
                 let uu____3190 =
                   let uu____3197 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3197  in
                 bind uu____3190
                   (fun uu____3216  ->
                      match uu____3216 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3230 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3233 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3230
                              FStar_Parser_Const.effect_Tot_lid uu____3233 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3247 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3247 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3269 =
                                   let uu____3270 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3270.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3269
                                  in
                               let uu____3283 = set_solution goal tm  in
                               bind uu____3283
                                 (fun uu____3292  ->
                                    let uu____3293 =
                                      let uu____3296 =
                                        bnorm_goal
                                          (let uu___124_3299 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___124_3299.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___124_3299.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___124_3299.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3296  in
                                    bind uu____3293
                                      (fun uu____3306  ->
                                         let uu____3307 =
                                           let uu____3312 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3312, b)  in
                                         ret uu____3307)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3321 =
                let uu____3322 = FStar_Tactics_Types.goal_env goal  in
                let uu____3323 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3322 uu____3323  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3321))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3341 = cur_goal ()  in
    bind uu____3341
      (fun goal  ->
         mlog
           (fun uu____3348  ->
              let uu____3349 =
                let uu____3350 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3350  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3349)
           (fun uu____3355  ->
              let steps =
                let uu____3359 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3359
                 in
              let t =
                let uu____3363 = FStar_Tactics_Types.goal_env goal  in
                let uu____3364 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3363 uu____3364  in
              let uu____3365 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3365))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3389 =
          mlog
            (fun uu____3394  ->
               let uu____3395 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3395)
            (fun uu____3397  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3403 -> g.FStar_Tactics_Types.opts
                      | uu____3406 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3411  ->
                         let uu____3412 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3412)
                      (fun uu____3415  ->
                         let uu____3416 = __tc e t  in
                         bind uu____3416
                           (fun uu____3437  ->
                              match uu____3437 with
                              | (t1,uu____3447,uu____3448) ->
                                  let steps =
                                    let uu____3452 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3452
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3389
  
let (refine_intro : unit -> unit tac) =
  fun uu____3466  ->
    let uu____3469 =
      let uu____3472 = cur_goal ()  in
      bind uu____3472
        (fun g  ->
           let uu____3479 =
             let uu____3490 = FStar_Tactics_Types.goal_env g  in
             let uu____3491 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3490 uu____3491
              in
           match uu____3479 with
           | (uu____3494,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3519 =
                 let uu____3524 =
                   let uu____3529 =
                     let uu____3530 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3530]  in
                   FStar_Syntax_Subst.open_term uu____3529 phi  in
                 match uu____3524 with
                 | (bvs,phi1) ->
                     let uu____3549 =
                       let uu____3550 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3550  in
                     (uu____3549, phi1)
                  in
               (match uu____3519 with
                | (bv1,phi1) ->
                    let uu____3563 =
                      let uu____3566 = FStar_Tactics_Types.goal_env g  in
                      let uu____3567 =
                        let uu____3568 =
                          let uu____3571 =
                            let uu____3572 =
                              let uu____3579 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3579)  in
                            FStar_Syntax_Syntax.NT uu____3572  in
                          [uu____3571]  in
                        FStar_Syntax_Subst.subst uu____3568 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3566
                        uu____3567 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3563
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3587  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3469
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3606 = cur_goal ()  in
      bind uu____3606
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3614 = FStar_Tactics_Types.goal_env goal  in
               let uu____3615 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3614 uu____3615
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3617 = __tc env t  in
           bind uu____3617
             (fun uu____3636  ->
                match uu____3636 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3651  ->
                         let uu____3652 =
                           let uu____3653 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3653 typ  in
                         let uu____3654 =
                           let uu____3655 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3655
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3652 uu____3654)
                      (fun uu____3658  ->
                         let uu____3659 =
                           let uu____3662 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3662 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3659
                           (fun uu____3664  ->
                              mlog
                                (fun uu____3668  ->
                                   let uu____3669 =
                                     let uu____3670 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3670 typ  in
                                   let uu____3671 =
                                     let uu____3672 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3673 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3672 uu____3673  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3669 uu____3671)
                                (fun uu____3676  ->
                                   let uu____3677 =
                                     let uu____3680 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3681 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3680 typ uu____3681  in
                                   bind uu____3677
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3687 =
                                             let uu____3688 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3688 t1  in
                                           let uu____3689 =
                                             let uu____3690 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3690 typ  in
                                           let uu____3691 =
                                             let uu____3692 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3693 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3692 uu____3693  in
                                           let uu____3694 =
                                             let uu____3695 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3696 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3695 uu____3696  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3687 uu____3689 uu____3691
                                             uu____3694)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3711 =
        mlog
          (fun uu____3716  ->
             let uu____3717 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3717)
          (fun uu____3720  ->
             let uu____3721 =
               let uu____3728 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3728  in
             bind uu____3721
               (fun uu___89_3737  ->
                  match uu___89_3737 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3747  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3750  ->
                           let uu____3751 =
                             let uu____3758 =
                               let uu____3761 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3761
                                 (fun uu____3766  ->
                                    let uu____3767 = refine_intro ()  in
                                    bind uu____3767
                                      (fun uu____3771  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3758  in
                           bind uu____3751
                             (fun uu___88_3778  ->
                                match uu___88_3778 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3786 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3711
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3815 =
             let uu____3818 =
               let uu____3821 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3821  in
             FStar_Util.set_elements uu____3818  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3815
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
          let uu____3899 = f x  in
          bind uu____3899
            (fun y  ->
               let uu____3907 = mapM f xs  in
               bind uu____3907 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3927 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3947 = cur_goal ()  in
        bind uu____3947
          (fun goal  ->
             mlog
               (fun uu____3954  ->
                  let uu____3955 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3955)
               (fun uu____3958  ->
                  let uu____3959 =
                    let uu____3964 =
                      let uu____3967 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3967  in
                    trytac_exn uu____3964  in
                  bind uu____3959
                    (fun uu___90_3974  ->
                       match uu___90_3974 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3982  ->
                                let uu____3983 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3983)
                             (fun uu____3986  ->
                                let uu____3987 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3987 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____4011  ->
                                         let uu____4012 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____4012)
                                      (fun uu____4015  ->
                                         let uu____4016 =
                                           let uu____4017 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____4017  in
                                         if uu____4016
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____4021 =
                                              let uu____4028 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____4028
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____4021
                                              (fun uu____4039  ->
                                                 match uu____4039 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____4066 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____4066
                                                        in
                                                     let uu____4069 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____4069
                                                       (fun uu____4077  ->
                                                          let u1 =
                                                            let uu____4079 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4079
                                                              u
                                                             in
                                                          let uu____4080 =
                                                            let uu____4081 =
                                                              let uu____4084
                                                                =
                                                                let uu____4085
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4085
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4084
                                                               in
                                                            uu____4081.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4080
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4113)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4137
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4137
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4141
                                                                    =
                                                                    let uu____4144
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___125_4147
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___125_4147.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___125_4147.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4144]
                                                                     in
                                                                    add_goals
                                                                    uu____4141))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4202 =
        mlog
          (fun uu____4207  ->
             let uu____4208 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4208)
          (fun uu____4211  ->
             let uu____4212 = cur_goal ()  in
             bind uu____4212
               (fun goal  ->
                  let uu____4218 =
                    let uu____4227 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4227 tm  in
                  bind uu____4218
                    (fun uu____4241  ->
                       match uu____4241 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4254 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4254 typ  in
                           let uu____4255 =
                             let uu____4258 =
                               let uu____4261 = __apply uopt tm1 typ1  in
                               bind uu____4261
                                 (fun uu____4266  ->
                                    let uu____4267 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4267 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4258  in
                           let uu____4268 =
                             let uu____4271 =
                               let uu____4272 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4272 tm1  in
                             let uu____4273 =
                               let uu____4274 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4274 typ1  in
                             let uu____4275 =
                               let uu____4276 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4277 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4276 uu____4277  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4271 uu____4273 uu____4275
                              in
                           try_unif uu____4255 uu____4268)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4202
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4300 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4300
    then
      let uu____4307 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4322 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4361 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4307 with
      | (pre,post) ->
          let post1 =
            let uu____4391 =
              let uu____4400 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4400]  in
            FStar_Syntax_Util.mk_app post uu____4391  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4424 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4424
       then
         let uu____4431 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4431
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4464 =
      let uu____4467 =
        mlog
          (fun uu____4472  ->
             let uu____4473 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4473)
          (fun uu____4477  ->
             let is_unit_t t =
               let uu____4484 =
                 let uu____4485 = FStar_Syntax_Subst.compress t  in
                 uu____4485.FStar_Syntax_Syntax.n  in
               match uu____4484 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4489 -> false  in
             let uu____4490 = cur_goal ()  in
             bind uu____4490
               (fun goal  ->
                  let uu____4496 =
                    let uu____4505 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4505 tm  in
                  bind uu____4496
                    (fun uu____4520  ->
                       match uu____4520 with
                       | (tm1,t,guard) ->
                           let uu____4532 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4532 with
                            | (bs,comp) ->
                                let uu____4559 = lemma_or_sq comp  in
                                (match uu____4559 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4578 =
                                       FStar_List.fold_left
                                         (fun uu____4620  ->
                                            fun uu____4621  ->
                                              match (uu____4620, uu____4621)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4712 =
                                                    is_unit_t b_t  in
                                                  if uu____4712
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4742 =
                                                       let uu____4755 =
                                                         let uu____4756 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4756.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4759 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4755
                                                         uu____4759 b_t
                                                        in
                                                     match uu____4742 with
                                                     | (u,uu____4775,g_u) ->
                                                         let uu____4789 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4789,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4578 with
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
                                          let uu____4850 =
                                            let uu____4853 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4854 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4855 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4853 uu____4854
                                              uu____4855
                                             in
                                          bind uu____4850
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4863 =
                                                   let uu____4864 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4864 tm1  in
                                                 let uu____4865 =
                                                   let uu____4866 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4867 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4866 uu____4867
                                                    in
                                                 let uu____4868 =
                                                   let uu____4869 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4870 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4869 uu____4870
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4863 uu____4865
                                                   uu____4868
                                               else
                                                 (let uu____4872 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4872
                                                    (fun uu____4877  ->
                                                       let uu____4878 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4878
                                                         (fun uu____4886  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4911
                                                                  =
                                                                  let uu____4914
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4914
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4911
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
                                                                   let uu____4949
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4949)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4965
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4965
                                                              with
                                                              | (hd1,uu____4981)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5003)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5024
                                                                    -> false)
                                                               in
                                                            let uu____5025 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5088
                                                                     ->
                                                                    match uu____5088
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5111
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5111
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5137)
                                                                    ->
                                                                    let uu____5158
                                                                    =
                                                                    let uu____5159
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5159.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5158
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5173)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___128_5197
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___128_5197.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___128_5197.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___128_5197.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5210
                                                                    ->
                                                                    let env =
                                                                    let uu___129_5212
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___129_5212.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5214
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5214
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
                                                                    let uu____5217
                                                                    =
                                                                    let uu____5224
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5224
                                                                    term1  in
                                                                    match uu____5217
                                                                    with
                                                                    | 
                                                                    (uu____5225,uu____5226,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5228
                                                                    =
                                                                    let uu____5233
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5233
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5228
                                                                    (fun
                                                                    uu___91_5245
                                                                     ->
                                                                    match uu___91_5245
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
                                                            bind uu____5025
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5313
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5313
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5335
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5335
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5396
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5396
                                                                    then
                                                                    let uu____5399
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5399
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
                                                                    let uu____5413
                                                                    =
                                                                    let uu____5414
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5414
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5413)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5415
                                                                   =
                                                                   let uu____5418
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5418
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5415
                                                                   (fun
                                                                    uu____5421
                                                                     ->
                                                                    let uu____5422
                                                                    =
                                                                    let uu____5425
                                                                    =
                                                                    let uu____5426
                                                                    =
                                                                    let uu____5427
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5428
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5427
                                                                    uu____5428
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5426
                                                                     in
                                                                    if
                                                                    uu____5425
                                                                    then
                                                                    let uu____5431
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5431
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5422
                                                                    (fun
                                                                    uu____5435
                                                                     ->
                                                                    let uu____5436
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5436
                                                                    (fun
                                                                    uu____5440
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4467  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4464
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5462 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5462 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5472::(e1,uu____5474)::(e2,uu____5476)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5519 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5543 = destruct_eq' typ  in
    match uu____5543 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5573 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5573 with
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
        let uu____5635 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5635 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5683 = aux e'  in
               FStar_Util.map_opt uu____5683
                 (fun uu____5707  ->
                    match uu____5707 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5728 = aux e  in
      FStar_Util.map_opt uu____5728
        (fun uu____5752  ->
           match uu____5752 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5819 =
            let uu____5828 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5828  in
          FStar_Util.map_opt uu____5819
            (fun uu____5843  ->
               match uu____5843 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___130_5862 = bv  in
                     let uu____5863 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___130_5862.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___130_5862.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5863
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___131_5871 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5872 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5879 =
                       let uu____5882 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5882  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___131_5871.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5872;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5879;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___131_5871.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___131_5871.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___131_5871.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___132_5883 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___132_5883.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___132_5883.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___132_5883.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5893 =
      let uu____5896 = cur_goal ()  in
      bind uu____5896
        (fun goal  ->
           let uu____5904 = h  in
           match uu____5904 with
           | (bv,uu____5908) ->
               mlog
                 (fun uu____5912  ->
                    let uu____5913 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5914 =
                      let uu____5915 = FStar_Tactics_Types.goal_env goal  in
                      tts uu____5915 bv.FStar_Syntax_Syntax.sort  in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5913
                      uu____5914)
                 (fun uu____5918  ->
                    let uu____5919 =
                      let uu____5928 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5928  in
                    match uu____5919 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5949 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5949 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5964 =
                               let uu____5965 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5965.FStar_Syntax_Syntax.n  in
                             (match uu____5964 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___133_5982 = bv1  in
                                    let uu____5983 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___133_5982.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___133_5982.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5983
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___134_5991 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5992 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5999 =
                                      let uu____6002 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6002
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___134_5991.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5992;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5999;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___134_5991.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___134_5991.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___134_5991.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___135_6005 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___135_6005.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___135_6005.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___135_6005.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6006 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6007 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5893
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6032 =
        let uu____6035 = cur_goal ()  in
        bind uu____6035
          (fun goal  ->
             let uu____6046 = b  in
             match uu____6046 with
             | (bv,uu____6050) ->
                 let bv' =
                   let uu____6052 =
                     let uu___136_6053 = bv  in
                     let uu____6054 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6054;
                       FStar_Syntax_Syntax.index =
                         (uu___136_6053.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___136_6053.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6052  in
                 let s1 =
                   let uu____6058 =
                     let uu____6059 =
                       let uu____6066 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6066)  in
                     FStar_Syntax_Syntax.NT uu____6059  in
                   [uu____6058]  in
                 let uu____6071 = subst_goal bv bv' s1 goal  in
                 (match uu____6071 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6032
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6090 =
      let uu____6093 = cur_goal ()  in
      bind uu____6093
        (fun goal  ->
           let uu____6102 = b  in
           match uu____6102 with
           | (bv,uu____6106) ->
               let uu____6107 =
                 let uu____6116 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6116  in
               (match uu____6107 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6137 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6137 with
                     | (ty,u) ->
                         let uu____6146 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6146
                           (fun uu____6164  ->
                              match uu____6164 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___137_6174 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___137_6174.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___137_6174.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6178 =
                                      let uu____6179 =
                                        let uu____6186 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6186)  in
                                      FStar_Syntax_Syntax.NT uu____6179  in
                                    [uu____6178]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___138_6198 = b1  in
                                         let uu____6199 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___138_6198.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___138_6198.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6199
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6206  ->
                                       let new_goal =
                                         let uu____6208 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6209 =
                                           let uu____6210 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6210
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6208 uu____6209
                                          in
                                       let uu____6211 = add_goals [new_goal]
                                          in
                                       bind uu____6211
                                         (fun uu____6216  ->
                                            let uu____6217 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6217
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6090
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6240 =
        let uu____6243 = cur_goal ()  in
        bind uu____6243
          (fun goal  ->
             let uu____6252 = b  in
             match uu____6252 with
             | (bv,uu____6256) ->
                 let uu____6257 =
                   let uu____6266 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6266  in
                 (match uu____6257 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6290 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6290
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___139_6295 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___139_6295.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___139_6295.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6297 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6297))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6240
  
let (revert : unit -> unit tac) =
  fun uu____6308  ->
    let uu____6311 = cur_goal ()  in
    bind uu____6311
      (fun goal  ->
         let uu____6317 =
           let uu____6324 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6324  in
         match uu____6317 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6340 =
                 let uu____6343 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6343  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6340
                in
             let uu____6352 = new_uvar "revert" env' typ'  in
             bind uu____6352
               (fun uu____6367  ->
                  match uu____6367 with
                  | (r,u_r) ->
                      let uu____6376 =
                        let uu____6379 =
                          let uu____6380 =
                            let uu____6381 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6381.FStar_Syntax_Syntax.pos  in
                          let uu____6384 =
                            let uu____6389 =
                              let uu____6390 =
                                let uu____6397 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6397  in
                              [uu____6390]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6389  in
                          uu____6384 FStar_Pervasives_Native.None uu____6380
                           in
                        set_solution goal uu____6379  in
                      bind uu____6376
                        (fun uu____6414  ->
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
      let uu____6426 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6426
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6439 = cur_goal ()  in
    bind uu____6439
      (fun goal  ->
         mlog
           (fun uu____6447  ->
              let uu____6448 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6449 =
                let uu____6450 =
                  let uu____6451 =
                    let uu____6458 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6458  in
                  FStar_All.pipe_right uu____6451 FStar_List.length  in
                FStar_All.pipe_right uu____6450 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6448 uu____6449)
           (fun uu____6471  ->
              let uu____6472 =
                let uu____6481 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6481  in
              match uu____6472 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6520 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6520
                        then
                          let uu____6523 =
                            let uu____6524 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6524
                             in
                          fail uu____6523
                        else check1 bvs2
                     in
                  let uu____6526 =
                    let uu____6527 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6527  in
                  if uu____6526
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6531 = check1 bvs  in
                     bind uu____6531
                       (fun uu____6537  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6539 =
                            let uu____6546 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6546  in
                          bind uu____6539
                            (fun uu____6555  ->
                               match uu____6555 with
                               | (ut,uvar_ut) ->
                                   let uu____6564 = set_solution goal ut  in
                                   bind uu____6564
                                     (fun uu____6569  ->
                                        let uu____6570 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6570))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6577  ->
    let uu____6580 = cur_goal ()  in
    bind uu____6580
      (fun goal  ->
         let uu____6586 =
           let uu____6593 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6593  in
         match uu____6586 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6601) ->
             let uu____6606 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6606)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6616 = cur_goal ()  in
    bind uu____6616
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6626 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6626  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6629  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6639 = cur_goal ()  in
    bind uu____6639
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6649 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6649  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6652  -> add_goals [g']))
  
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
            let uu____6692 = FStar_Syntax_Subst.compress t  in
            uu____6692.FStar_Syntax_Syntax.n  in
          let uu____6695 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___143_6701 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___143_6701.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___143_6701.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6695
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6717 =
                   let uu____6718 = FStar_Syntax_Subst.compress t1  in
                   uu____6718.FStar_Syntax_Syntax.n  in
                 match uu____6717 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6745 = ff hd1  in
                     bind uu____6745
                       (fun hd2  ->
                          let fa uu____6767 =
                            match uu____6767 with
                            | (a,q) ->
                                let uu____6780 = ff a  in
                                bind uu____6780 (fun a1  -> ret (a1, q))
                             in
                          let uu____6793 = mapM fa args  in
                          bind uu____6793
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6859 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6859 with
                      | (bs1,t') ->
                          let uu____6868 =
                            let uu____6871 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6871 t'  in
                          bind uu____6868
                            (fun t''  ->
                               let uu____6875 =
                                 let uu____6876 =
                                   let uu____6893 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6900 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6893, uu____6900, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6876  in
                               ret uu____6875))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6969 = ff hd1  in
                     bind uu____6969
                       (fun hd2  ->
                          let ffb br =
                            let uu____6984 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6984 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7016 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7016  in
                                let uu____7017 = ff1 e  in
                                bind uu____7017
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7032 = mapM ffb brs  in
                          bind uu____7032
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7076;
                          FStar_Syntax_Syntax.lbtyp = uu____7077;
                          FStar_Syntax_Syntax.lbeff = uu____7078;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7080;
                          FStar_Syntax_Syntax.lbpos = uu____7081;_}::[]),e)
                     ->
                     let lb =
                       let uu____7106 =
                         let uu____7107 = FStar_Syntax_Subst.compress t1  in
                         uu____7107.FStar_Syntax_Syntax.n  in
                       match uu____7106 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7111) -> lb
                       | uu____7124 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7133 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7133
                         (fun def1  ->
                            ret
                              (let uu___140_7139 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___140_7139.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___140_7139.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___140_7139.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___140_7139.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___140_7139.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___140_7139.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7140 = fflb lb  in
                     bind uu____7140
                       (fun lb1  ->
                          let uu____7150 =
                            let uu____7155 =
                              let uu____7156 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7156]  in
                            FStar_Syntax_Subst.open_term uu____7155 e  in
                          match uu____7150 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7180 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7180  in
                              let uu____7181 = ff1 e1  in
                              bind uu____7181
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7222 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7222
                         (fun def  ->
                            ret
                              (let uu___141_7228 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___141_7228.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___141_7228.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___141_7228.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___141_7228.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___141_7228.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___141_7228.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7229 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7229 with
                      | (lbs1,e1) ->
                          let uu____7244 = mapM fflb lbs1  in
                          bind uu____7244
                            (fun lbs2  ->
                               let uu____7256 = ff e1  in
                               bind uu____7256
                                 (fun e2  ->
                                    let uu____7264 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7264 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7332 = ff t2  in
                     bind uu____7332
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7363 = ff t2  in
                     bind uu____7363
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7370 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___142_7377 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___142_7377.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___142_7377.FStar_Syntax_Syntax.vars)
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
            let uu____7414 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7414 with
            | (t1,lcomp,g) ->
                let uu____7426 =
                  (let uu____7429 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7429) ||
                    (let uu____7431 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7431)
                   in
                if uu____7426
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7439 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7439
                       (fun uu____7455  ->
                          match uu____7455 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7468  ->
                                    let uu____7469 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7470 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7469 uu____7470);
                               (let uu____7471 =
                                  let uu____7474 =
                                    let uu____7475 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7475 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7474
                                    opts
                                   in
                                bind uu____7471
                                  (fun uu____7478  ->
                                     let uu____7479 =
                                       bind tau
                                         (fun uu____7485  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7491  ->
                                                 let uu____7492 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7493 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7492 uu____7493);
                                            ret ut1)
                                        in
                                     focus uu____7479))))
                      in
                   let uu____7494 = trytac' rewrite_eq  in
                   bind uu____7494
                     (fun x  ->
                        match x with
                        | FStar_Util.Inl "SKIP" -> ret t1
                        | FStar_Util.Inl e -> fail e
                        | FStar_Util.Inr x1 -> ret x1))
  
type ctrl = FStar_BigInt.t
let (keepGoing : ctrl) = FStar_BigInt.zero 
let (proceedToNextSubtree : FStar_BigInt.bigint) = FStar_BigInt.one 
let (globalStop : FStar_BigInt.bigint) =
  FStar_BigInt.succ_big_int FStar_BigInt.one 
type rewrite_result = Prims.bool
let (skipThisTerm : Prims.bool) = false 
let (rewroteThisTerm : Prims.bool) = true 
type 'a ctrl_tac = ('a,ctrl) FStar_Pervasives_Native.tuple2 tac
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
          let uu____7692 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7692
            (fun t1  ->
               let uu____7700 =
                 f env
                   (let uu___146_7709 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___146_7709.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___146_7709.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7700
                 (fun uu____7725  ->
                    match uu____7725 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7748 =
                               let uu____7749 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7749.FStar_Syntax_Syntax.n  in
                             match uu____7748 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7782 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7782
                                   (fun uu____7807  ->
                                      match uu____7807 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7823 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7823
                                            (fun uu____7850  ->
                                               match uu____7850 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___144_7880 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___144_7880.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___144_7880.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7916 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7916 with
                                  | (bs1,t') ->
                                      let uu____7931 =
                                        let uu____7938 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7938 ctrl1 t'
                                         in
                                      bind uu____7931
                                        (fun uu____7956  ->
                                           match uu____7956 with
                                           | (t'',ctrl2) ->
                                               let uu____7971 =
                                                 let uu____7978 =
                                                   let uu___145_7981 = t4  in
                                                   let uu____7984 =
                                                     let uu____7985 =
                                                       let uu____8002 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8009 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8002,
                                                         uu____8009, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7985
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7984;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___145_7981.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___145_7981.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7978, ctrl2)  in
                                               ret uu____7971))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8056 -> ret (t3, ctrl1))))

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
              let uu____8099 = ctrl_tac_fold f env ctrl t  in
              bind uu____8099
                (fun uu____8123  ->
                   match uu____8123 with
                   | (t1,ctrl1) ->
                       let uu____8138 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8138
                         (fun uu____8165  ->
                            match uu____8165 with
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
              let uu____8247 =
                let uu____8254 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8254
                  (fun uu____8263  ->
                     let uu____8264 = ctrl t1  in
                     bind uu____8264
                       (fun res  ->
                          let uu____8287 = trivial ()  in
                          bind uu____8287 (fun uu____8295  -> ret res)))
                 in
              bind uu____8247
                (fun uu____8311  ->
                   match uu____8311 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8335 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8335 with
                          | (t2,lcomp,g) ->
                              let uu____8351 =
                                (let uu____8354 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8354) ||
                                  (let uu____8356 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8356)
                                 in
                              if uu____8351
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8369 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8369
                                   (fun uu____8389  ->
                                      match uu____8389 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8406  ->
                                                let uu____8407 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8408 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8407 uu____8408);
                                           (let uu____8409 =
                                              let uu____8412 =
                                                let uu____8413 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8413 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8412 opts
                                               in
                                            bind uu____8409
                                              (fun uu____8420  ->
                                                 let uu____8421 =
                                                   bind rewriter
                                                     (fun uu____8435  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8441  ->
                                                             let uu____8442 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8443 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8442
                                                               uu____8443);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8421)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8484 =
        bind get
          (fun ps  ->
             let uu____8494 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8494 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8531  ->
                       let uu____8532 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8532);
                  bind dismiss_all
                    (fun uu____8535  ->
                       let uu____8536 =
                         let uu____8543 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8543
                           keepGoing gt1
                          in
                       bind uu____8536
                         (fun uu____8555  ->
                            match uu____8555 with
                            | (gt',uu____8563) ->
                                (log ps
                                   (fun uu____8567  ->
                                      let uu____8568 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8568);
                                 (let uu____8569 = push_goals gs  in
                                  bind uu____8569
                                    (fun uu____8574  ->
                                       let uu____8575 =
                                         let uu____8578 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8578]  in
                                       add_goals uu____8575)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8484
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8601 =
        bind get
          (fun ps  ->
             let uu____8611 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8611 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8648  ->
                       let uu____8649 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8649);
                  bind dismiss_all
                    (fun uu____8652  ->
                       let uu____8653 =
                         let uu____8656 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8656 gt1
                          in
                       bind uu____8653
                         (fun gt'  ->
                            log ps
                              (fun uu____8664  ->
                                 let uu____8665 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8665);
                            (let uu____8666 = push_goals gs  in
                             bind uu____8666
                               (fun uu____8671  ->
                                  let uu____8672 =
                                    let uu____8675 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8675]  in
                                  add_goals uu____8672))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8601
  
let (trefl : unit -> unit tac) =
  fun uu____8686  ->
    let uu____8689 =
      let uu____8692 = cur_goal ()  in
      bind uu____8692
        (fun g  ->
           let uu____8710 =
             let uu____8715 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8715  in
           match uu____8710 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8723 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8723 with
                | (hd1,args) ->
                    let uu____8756 =
                      let uu____8767 =
                        let uu____8768 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8768.FStar_Syntax_Syntax.n  in
                      (uu____8767, args)  in
                    (match uu____8756 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8780::(l,uu____8782)::(r,uu____8784)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8811 =
                           let uu____8814 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8814 l r  in
                         bind uu____8811
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8821 =
                                  let uu____8822 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8822 l  in
                                let uu____8823 =
                                  let uu____8824 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8824 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8821 uu____8823
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8827) ->
                         let uu____8840 =
                           let uu____8841 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8841 t  in
                         fail1 "trefl: not an equality (%s)" uu____8840))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8689
  
let (dup : unit -> unit tac) =
  fun uu____8854  ->
    let uu____8857 = cur_goal ()  in
    bind uu____8857
      (fun g  ->
         let uu____8863 =
           let uu____8870 = FStar_Tactics_Types.goal_env g  in
           let uu____8871 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8870 uu____8871  in
         bind uu____8863
           (fun uu____8880  ->
              match uu____8880 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___147_8890 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___147_8890.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___147_8890.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___147_8890.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8893  ->
                       let uu____8894 =
                         let uu____8897 = FStar_Tactics_Types.goal_env g  in
                         let uu____8898 =
                           let uu____8899 =
                             let uu____8900 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8901 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8900
                               uu____8901
                              in
                           let uu____8902 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8903 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8899 uu____8902 u
                             uu____8903
                            in
                         add_irrelevant_goal "dup equation" uu____8897
                           uu____8898 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8894
                         (fun uu____8906  ->
                            let uu____8907 = add_goals [g']  in
                            bind uu____8907 (fun uu____8911  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8918  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___148_8935 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___148_8935.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___148_8935.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___148_8935.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___148_8935.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___148_8935.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___148_8935.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___148_8935.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___148_8935.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___148_8935.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___148_8935.FStar_Tactics_Types.freshness)
                })
         | uu____8936 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8945  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___149_8958 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___149_8958.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___149_8958.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___149_8958.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___149_8958.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___149_8958.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___149_8958.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___149_8958.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___149_8958.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___149_8958.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___149_8958.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8965  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8972 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8992 =
      let uu____8999 = cur_goal ()  in
      bind uu____8999
        (fun g  ->
           let uu____9009 =
             let uu____9018 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9018 t  in
           bind uu____9009
             (fun uu____9046  ->
                match uu____9046 with
                | (t1,typ,guard) ->
                    let uu____9062 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9062 with
                     | (hd1,args) ->
                         let uu____9105 =
                           let uu____9118 =
                             let uu____9119 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9119.FStar_Syntax_Syntax.n  in
                           (uu____9118, args)  in
                         (match uu____9105 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9138)::(q,uu____9140)::[]) when
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
                                let uu____9178 =
                                  let uu____9179 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9179
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9178
                                 in
                              let g2 =
                                let uu____9181 =
                                  let uu____9182 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9182
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9181
                                 in
                              bind __dismiss
                                (fun uu____9189  ->
                                   let uu____9190 = add_goals [g1; g2]  in
                                   bind uu____9190
                                     (fun uu____9199  ->
                                        let uu____9200 =
                                          let uu____9205 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9206 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9205, uu____9206)  in
                                        ret uu____9200))
                          | uu____9211 ->
                              let uu____9224 =
                                let uu____9225 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9225 typ  in
                              fail1 "Not a disjunction: %s" uu____9224))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8992
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9255 =
      let uu____9258 = cur_goal ()  in
      bind uu____9258
        (fun g  ->
           FStar_Options.push ();
           (let uu____9271 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9271);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___150_9278 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___150_9278.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___150_9278.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___150_9278.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9255
  
let (top_env : unit -> env tac) =
  fun uu____9290  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9303  ->
    let uu____9306 = cur_goal ()  in
    bind uu____9306
      (fun g  ->
         let uu____9312 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9312)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9321  ->
    let uu____9324 = cur_goal ()  in
    bind uu____9324
      (fun g  ->
         let uu____9330 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9330)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9339  ->
    let uu____9342 = cur_goal ()  in
    bind uu____9342
      (fun g  ->
         let uu____9348 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9348)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9365 =
        let uu____9368 = cur_goal ()  in
        bind uu____9368
          (fun goal  ->
             let env =
               let uu____9376 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9376 ty  in
             let uu____9377 = __tc env tm  in
             bind uu____9377
               (fun uu____9397  ->
                  match uu____9397 with
                  | (tm1,typ,guard) ->
                      let uu____9409 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9409 (fun uu____9413  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9365
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9436 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9442 =
              let uu____9449 =
                let uu____9450 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9450
                 in
              new_uvar "uvar_env.2" env uu____9449  in
            bind uu____9442
              (fun uu____9466  ->
                 match uu____9466 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9436
        (fun typ  ->
           let uu____9478 = new_uvar "uvar_env" env typ  in
           bind uu____9478
             (fun uu____9492  -> match uu____9492 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9510 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9529 -> g.FStar_Tactics_Types.opts
             | uu____9532 -> FStar_Options.peek ()  in
           let uu____9535 = FStar_Syntax_Util.head_and_args t  in
           match uu____9535 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9553);
                FStar_Syntax_Syntax.pos = uu____9554;
                FStar_Syntax_Syntax.vars = uu____9555;_},uu____9556)
               ->
               let env1 =
                 let uu___151_9598 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___151_9598.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___151_9598.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___151_9598.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___151_9598.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___151_9598.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___151_9598.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___151_9598.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___151_9598.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___151_9598.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___151_9598.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___151_9598.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___151_9598.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___151_9598.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___151_9598.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___151_9598.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___151_9598.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___151_9598.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___151_9598.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___151_9598.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___151_9598.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___151_9598.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___151_9598.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___151_9598.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___151_9598.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___151_9598.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___151_9598.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___151_9598.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___151_9598.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___151_9598.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___151_9598.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___151_9598.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___151_9598.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___151_9598.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___151_9598.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___151_9598.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___151_9598.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___151_9598.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___151_9598.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9600 =
                 let uu____9603 = bnorm_goal g  in [uu____9603]  in
               add_goals uu____9600
           | uu____9604 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9510
  
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
          (fun uu____9665  ->
             let uu____9666 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9666
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
        (fun uu____9687  ->
           let uu____9688 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9688)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9698 =
      mlog
        (fun uu____9703  ->
           let uu____9704 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9704)
        (fun uu____9707  ->
           let uu____9708 = cur_goal ()  in
           bind uu____9708
             (fun g  ->
                let uu____9714 =
                  let uu____9723 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9723 ty  in
                bind uu____9714
                  (fun uu____9735  ->
                     match uu____9735 with
                     | (ty1,uu____9745,guard) ->
                         let uu____9747 =
                           let uu____9750 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9750 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9747
                           (fun uu____9753  ->
                              let uu____9754 =
                                let uu____9757 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9758 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9757 uu____9758 ty1  in
                              bind uu____9754
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9764 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9764
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
                                        let uu____9770 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9771 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9770 uu____9771
                                         in
                                      let nty =
                                        let uu____9773 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9773 ty1  in
                                      let uu____9774 =
                                        let uu____9777 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9777 ng nty  in
                                      bind uu____9774
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9783 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9783
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9698
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9805::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9833 = init xs  in x :: uu____9833
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9845 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9853) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____9910 = last args  in
          (match uu____9910 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____9932 =
                 let uu____9933 =
                   let uu____9938 =
                     let uu____9939 =
                       let uu____9944 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9944  in
                     uu____9939 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____9938, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____9933  in
               FStar_All.pipe_left ret uu____9932)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____9955,uu____9956) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10000 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10000 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10033 =
                      let uu____10034 =
                        let uu____10039 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10039)  in
                      FStar_Reflection_Data.Tv_Abs uu____10034  in
                    FStar_All.pipe_left ret uu____10033))
      | FStar_Syntax_Syntax.Tm_type uu____10042 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10062 ->
          let uu____10075 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10075 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10105 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10105 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10144 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10152 =
            let uu____10153 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10153  in
          FStar_All.pipe_left ret uu____10152
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10178 =
            let uu____10179 =
              let uu____10184 =
                let uu____10185 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10185  in
              (uu____10184, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10179  in
          FStar_All.pipe_left ret uu____10178
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10221 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10226 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10226 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10265 ->
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
             | FStar_Util.Inr uu____10295 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10299 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10299 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10319 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10323 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10377 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10377
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10396 =
                  let uu____10403 =
                    FStar_List.map
                      (fun uu____10415  ->
                         match uu____10415 with
                         | (p1,uu____10423) -> inspect_pat p1) ps
                     in
                  (fv, uu____10403)  in
                FStar_Reflection_Data.Pat_Cons uu____10396
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
              (fun uu___92_10517  ->
                 match uu___92_10517 with
                 | (pat,uu____10539,t4) ->
                     let uu____10557 = inspect_pat pat  in (uu____10557, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10566 ->
          ((let uu____10568 =
              let uu____10573 =
                let uu____10574 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10575 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10574 uu____10575
                 in
              (FStar_Errors.Warning_CantInspect, uu____10573)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10568);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9845
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10588 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10588
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10592 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10592
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10596 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10596
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10603 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10603
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10622 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10622
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10635 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10635
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10650 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10650
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10654 =
          let uu____10655 =
            let uu____10662 =
              let uu____10663 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10663  in
            FStar_Syntax_Syntax.mk uu____10662  in
          uu____10655 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10654
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10671 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10671
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10680 =
          let uu____10681 =
            let uu____10688 =
              let uu____10689 =
                let uu____10702 =
                  let uu____10705 =
                    let uu____10706 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10706]  in
                  FStar_Syntax_Subst.close uu____10705 t2  in
                ((false, [lb]), uu____10702)  in
              FStar_Syntax_Syntax.Tm_let uu____10689  in
            FStar_Syntax_Syntax.mk uu____10688  in
          uu____10681 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10680
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10740 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10740 with
         | (lbs,body) ->
             let uu____10755 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10755)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10789 =
                let uu____10790 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10790  in
              FStar_All.pipe_left wrap uu____10789
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10797 =
                let uu____10798 =
                  let uu____10811 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10827 = pack_pat p1  in
                         (uu____10827, false)) ps
                     in
                  (fv, uu____10811)  in
                FStar_Syntax_Syntax.Pat_cons uu____10798  in
              FStar_All.pipe_left wrap uu____10797
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
            (fun uu___93_10873  ->
               match uu___93_10873 with
               | (pat,t1) ->
                   let uu____10890 = pack_pat pat  in
                   (uu____10890, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10938 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10938
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10966 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10966
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11012 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11012
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11051 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11051
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11072 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11072 with
      | (u,ctx_uvars,g_u) ->
          let uu____11104 = FStar_List.hd ctx_uvars  in
          (match uu____11104 with
           | (ctx_uvar,uu____11118) ->
               let g =
                 let uu____11120 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11120 false
                  in
               (g, g_u))
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let uu____11140 = goal_of_goal_ty env typ  in
        match uu____11140 with
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
                FStar_Tactics_Types.psc =
                  FStar_TypeChecker_Normalize.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0")
              }  in
            let uu____11156 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11156)
  