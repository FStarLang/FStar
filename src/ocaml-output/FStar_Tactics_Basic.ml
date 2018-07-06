open Prims
type goal = FStar_Tactics_Types.goal
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Env.steps ->
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
    let uu____39 =
      let uu____40 = FStar_Tactics_Types.goal_env g  in
      let uu____41 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____40 uu____41  in
    FStar_Tactics_Types.goal_with_type g uu____39
  
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
      try (fun uu___355_154  -> match () with | () -> t.tac_f p) ()
      with
      | FStar_Errors.Err (uu____163,msg) ->
          FStar_Tactics_Result.Failed (msg, p)
      | FStar_Errors.Error (uu____165,msg,uu____167) ->
          FStar_Tactics_Result.Failed (msg, p)
      | e ->
          let uu____169 =
            let uu____174 = FStar_Util.message_of_exn e  in (uu____174, p)
             in
          FStar_Tactics_Result.Failed uu____169
  
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  -> if ps.FStar_Tactics_Types.tac_verb_dbg then f () else ()
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____246 = run t1 p  in
           match uu____246 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____253 = t2 a  in run uu____253 q
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
    let uu____273 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____273 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____291 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____292 =
      let uu____293 = check_goal_solved g  in
      match uu____293 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____297 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____297
       in
    FStar_Util.format2 "%s%s" uu____291 uu____292
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____308 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____308
      then goal_to_string_verbose g
      else
        (let w =
           let uu____311 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____311 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____315 = FStar_Tactics_Types.goal_env g  in
               tts uu____315 t
            in
         let uu____316 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____317 =
           let uu____318 = FStar_Tactics_Types.goal_env g  in
           tts uu____318
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____316 w uu____317)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____334 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____334
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____350 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____350
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____371 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____371
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____378) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____388) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____407 =
      let uu____408 = FStar_Tactics_Types.goal_env g  in
      let uu____409 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____408 uu____409  in
    FStar_Syntax_Util.un_squash uu____407
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____415 = get_phi g  in FStar_Option.isSome uu____415 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____441 =
            let uu____442 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____442  in
          if uu____441 then tacprint msg else ());
         ret ())
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____455 = goal_to_string ps goal  in tacprint uu____455
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____467 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____471 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____471))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____480  ->
    match uu____480 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____493 =
          let uu____496 =
            let uu____497 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____497 msg
             in
          let uu____498 =
            let uu____501 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____502 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____502
              else ""  in
            let uu____504 =
              let uu____507 =
                let uu____508 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____508
                then
                  let uu____509 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____509
                else ""  in
              let uu____511 =
                let uu____514 =
                  let uu____515 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____516 =
                    let uu____517 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____517  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____515
                    uu____516
                   in
                let uu____520 =
                  let uu____523 =
                    let uu____524 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____525 =
                      let uu____526 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____526  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____524
                      uu____525
                     in
                  [uu____523]  in
                uu____514 :: uu____520  in
              uu____507 :: uu____511  in
            uu____501 :: uu____504  in
          uu____496 :: uu____498  in
        FStar_String.concat "" uu____493
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____535 =
        let uu____536 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____536  in
      let uu____537 =
        let uu____542 =
          let uu____543 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____543  in
        FStar_Syntax_Print.binders_to_json uu____542  in
      FStar_All.pipe_right uu____535 uu____537  in
    let uu____544 =
      let uu____551 =
        let uu____558 =
          let uu____563 =
            let uu____564 =
              let uu____571 =
                let uu____576 =
                  let uu____577 =
                    let uu____578 = FStar_Tactics_Types.goal_env g  in
                    let uu____579 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____578 uu____579  in
                  FStar_Util.JsonStr uu____577  in
                ("witness", uu____576)  in
              let uu____580 =
                let uu____587 =
                  let uu____592 =
                    let uu____593 =
                      let uu____594 = FStar_Tactics_Types.goal_env g  in
                      let uu____595 = FStar_Tactics_Types.goal_type g  in
                      tts uu____594 uu____595  in
                    FStar_Util.JsonStr uu____593  in
                  ("type", uu____592)  in
                [uu____587]  in
              uu____571 :: uu____580  in
            FStar_Util.JsonAssoc uu____564  in
          ("goal", uu____563)  in
        [uu____558]  in
      ("hyps", g_binders) :: uu____551  in
    FStar_Util.JsonAssoc uu____544
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____628  ->
    match uu____628 with
    | (msg,ps) ->
        let uu____635 =
          let uu____642 =
            let uu____649 =
              let uu____656 =
                let uu____663 =
                  let uu____668 =
                    let uu____669 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____669  in
                  ("goals", uu____668)  in
                let uu____672 =
                  let uu____679 =
                    let uu____684 =
                      let uu____685 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____685  in
                    ("smt-goals", uu____684)  in
                  [uu____679]  in
                uu____663 :: uu____672  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____656
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____649  in
          let uu____708 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____721 =
                let uu____726 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____726)  in
              [uu____721]
            else []  in
          FStar_List.append uu____642 uu____708  in
        FStar_Util.JsonAssoc uu____635
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____756  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____779 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____779 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____797 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____797 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____851 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____851
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____859 . Prims.string -> Prims.string -> 'Auu____859 tac =
  fun msg  ->
    fun x  -> let uu____872 = FStar_Util.format1 msg x  in fail uu____872
  
let fail2 :
  'Auu____881 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____881 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____899 = FStar_Util.format2 msg x y  in fail uu____899
  
let fail3 :
  'Auu____910 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____910 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____933 = FStar_Util.format3 msg x y z  in fail uu____933
  
let fail4 :
  'Auu____946 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____946 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____974 = FStar_Util.format4 msg x y z w  in fail uu____974
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1007 = run t ps  in
         match uu____1007 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___356_1031 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___356_1031.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___356_1031.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___356_1031.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___356_1031.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___356_1031.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___356_1031.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___356_1031.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___356_1031.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___356_1031.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___356_1031.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___356_1031.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___356_1031.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1058 = catch t  in
    bind uu____1058
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1085 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___358_1116  ->
              match () with
              | () -> let uu____1121 = trytac t  in run uu____1121 ps) ()
         with
         | FStar_Errors.Err (uu____1137,msg) ->
             (log ps
                (fun uu____1141  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1146,msg,uu____1148) ->
             (log ps
                (fun uu____1151  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1184 = run t ps  in
           match uu____1184 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1203  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___359_1217 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1217.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1217.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1217.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___359_1217.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1217.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1217.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1217.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1217.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1217.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1217.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1217.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___359_1217.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1238 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1238
         then
           let uu____1239 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1240 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1239
             uu____1240
         else ());
        (try
           (fun uu___361_1247  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1254 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1254
                    then
                      let uu____1255 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1256 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1257 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1255
                        uu____1256 uu____1257
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1262 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1262 (fun uu____1266  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1273,msg) ->
             mlog
               (fun uu____1276  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1278  -> ret false)
         | FStar_Errors.Error (uu____1279,msg,r) ->
             mlog
               (fun uu____1284  ->
                  let uu____1285 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1285) (fun uu____1287  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___362_1298 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___362_1298.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___362_1298.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___362_1298.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___363_1301 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___363_1301.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___363_1301.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___363_1301.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___363_1301.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___363_1301.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___363_1301.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___363_1301.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___363_1301.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___363_1301.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___363_1301.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___363_1301.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___363_1301.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1324  ->
             (let uu____1326 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1326
              then
                (FStar_Options.push ();
                 (let uu____1328 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1330 = __do_unify env t1 t2  in
              bind uu____1330
                (fun r  ->
                   (let uu____1337 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1337 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1340  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___364_1347 = ps  in
         let uu____1348 =
           FStar_List.filter
             (fun g  ->
                let uu____1354 = check_goal_solved g  in
                FStar_Option.isNone uu____1354) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_1347.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___364_1347.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___364_1347.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1348;
           FStar_Tactics_Types.smt_goals =
             (uu___364_1347.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_1347.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_1347.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_1347.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_1347.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_1347.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_1347.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_1347.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___364_1347.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1371 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1371 with
      | FStar_Pervasives_Native.Some uu____1376 ->
          let uu____1377 =
            let uu____1378 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1378  in
          fail uu____1377
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1394 = FStar_Tactics_Types.goal_env goal  in
      let uu____1395 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1394 solution uu____1395
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1401 =
         let uu___365_1402 = p  in
         let uu____1403 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___365_1402.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___365_1402.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___365_1402.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1403;
           FStar_Tactics_Types.smt_goals =
             (uu___365_1402.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___365_1402.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___365_1402.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___365_1402.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___365_1402.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___365_1402.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___365_1402.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___365_1402.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___365_1402.FStar_Tactics_Types.local_state)
         }  in
       set uu____1401)
  
let (dismiss : unit -> unit tac) =
  fun uu____1412  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1419 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1440  ->
           let uu____1441 =
             let uu____1442 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1442  in
           let uu____1443 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1441 uu____1443)
        (fun uu____1446  ->
           let uu____1447 = trysolve goal solution  in
           bind uu____1447
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1455  -> remove_solved_goals)
                else
                  (let uu____1457 =
                     let uu____1458 =
                       let uu____1459 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1459 solution  in
                     let uu____1460 =
                       let uu____1461 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1462 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1461 uu____1462  in
                     let uu____1463 =
                       let uu____1464 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1465 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1464 uu____1465  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1458 uu____1460 uu____1463
                      in
                   fail uu____1457)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1480 = set_solution goal solution  in
      bind uu____1480
        (fun uu____1484  ->
           bind __dismiss (fun uu____1486  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___366_1493 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___366_1493.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___366_1493.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___366_1493.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___366_1493.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___366_1493.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___366_1493.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___366_1493.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___366_1493.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___366_1493.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___366_1493.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___366_1493.FStar_Tactics_Types.tac_verb_dbg);
            FStar_Tactics_Types.local_state =
              (uu___366_1493.FStar_Tactics_Types.local_state)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1512 = FStar_Options.defensive ()  in
    if uu____1512
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1517 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1517)
         in
      let b2 =
        b1 &&
          (let uu____1520 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1520)
         in
      let rec aux b3 e =
        let uu____1532 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1532 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1550 =
        (let uu____1553 = aux b2 env  in Prims.op_Negation uu____1553) &&
          (let uu____1555 = FStar_ST.op_Bang nwarn  in
           uu____1555 < (Prims.parse_int "5"))
         in
      (if uu____1550
       then
         ((let uu____1576 =
             let uu____1577 = FStar_Tactics_Types.goal_type g  in
             uu____1577.FStar_Syntax_Syntax.pos  in
           let uu____1580 =
             let uu____1585 =
               let uu____1586 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1586
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1585)  in
           FStar_Errors.log_issue uu____1576 uu____1580);
          (let uu____1587 =
             let uu____1588 = FStar_ST.op_Bang nwarn  in
             uu____1588 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1587))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___367_1648 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_1648.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_1648.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_1648.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___367_1648.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___367_1648.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_1648.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_1648.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_1648.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_1648.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_1648.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_1648.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___367_1648.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___368_1668 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1668.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1668.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1668.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___368_1668.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_1668.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1668.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1668.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1668.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___368_1668.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___368_1668.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_1668.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___368_1668.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1688 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1688.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1688.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1688.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___369_1688.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1688.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1688.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1688.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1688.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1688.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1688.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1688.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___369_1688.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___370_1708 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1708.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1708.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1708.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_1708.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___370_1708.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1708.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1708.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1708.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1708.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1708.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1708.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1708.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1719  -> add_goals [g]) 
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
        let uu____1747 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1747 with
        | (u,ctx_uvar,g_u) ->
            let uu____1781 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1781
              (fun uu____1790  ->
                 let uu____1791 =
                   let uu____1796 =
                     let uu____1797 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1797  in
                   (u, uu____1796)  in
                 ret uu____1791)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1815 = FStar_Syntax_Util.un_squash t  in
    match uu____1815 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1825 =
          let uu____1826 = FStar_Syntax_Subst.compress t'  in
          uu____1826.FStar_Syntax_Syntax.n  in
        (match uu____1825 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1830 -> false)
    | uu____1831 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1841 = FStar_Syntax_Util.un_squash t  in
    match uu____1841 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1851 =
          let uu____1852 = FStar_Syntax_Subst.compress t'  in
          uu____1852.FStar_Syntax_Syntax.n  in
        (match uu____1851 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1856 -> false)
    | uu____1857 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1868  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1879 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1879 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1886 = goal_to_string_verbose hd1  in
                    let uu____1887 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1886 uu____1887);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1894  ->
    let uu____1897 =
      bind get
        (fun ps  ->
           let uu____1903 = cur_goal ()  in
           bind uu____1903
             (fun g  ->
                (let uu____1910 =
                   let uu____1911 = FStar_Tactics_Types.goal_type g  in
                   uu____1911.FStar_Syntax_Syntax.pos  in
                 let uu____1914 =
                   let uu____1919 =
                     let uu____1920 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1920
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1919)  in
                 FStar_Errors.log_issue uu____1910 uu____1914);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1897
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1931  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___371_1941 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___371_1941.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___371_1941.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___371_1941.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___371_1941.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___371_1941.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___371_1941.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___371_1941.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___371_1941.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___371_1941.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___371_1941.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___371_1941.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___371_1941.FStar_Tactics_Types.local_state)
           }  in
         let uu____1942 = set ps1  in
         bind uu____1942
           (fun uu____1947  ->
              let uu____1948 = FStar_BigInt.of_int_fs n1  in ret uu____1948))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1955  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1963 = FStar_BigInt.of_int_fs n1  in ret uu____1963)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1976  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1984 = FStar_BigInt.of_int_fs n1  in ret uu____1984)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1997  ->
    let uu____2000 = cur_goal ()  in
    bind uu____2000 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2032 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2032 phi  in
          let uu____2033 = new_uvar reason env typ  in
          bind uu____2033
            (fun uu____2048  ->
               match uu____2048 with
               | (uu____2055,ctx_uvar) ->
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
             (fun uu____2100  ->
                let uu____2101 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2101)
             (fun uu____2104  ->
                let e1 =
                  let uu___372_2106 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___372_2106.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___372_2106.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___372_2106.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___372_2106.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___372_2106.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___372_2106.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___372_2106.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___372_2106.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___372_2106.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___372_2106.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___372_2106.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___372_2106.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___372_2106.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___372_2106.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___372_2106.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___372_2106.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___372_2106.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___372_2106.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___372_2106.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___372_2106.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___372_2106.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___372_2106.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___372_2106.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___372_2106.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___372_2106.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___372_2106.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___372_2106.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___372_2106.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___372_2106.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___372_2106.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___372_2106.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___372_2106.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___372_2106.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___372_2106.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___372_2106.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___372_2106.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___372_2106.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___372_2106.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___372_2106.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___372_2106.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___372_2106.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___374_2117  ->
                     match () with
                     | () ->
                         let uu____2126 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2126) ()
                with
                | FStar_Errors.Err (uu____2153,msg) ->
                    let uu____2155 = tts e1 t  in
                    let uu____2156 =
                      let uu____2157 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2157
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2155 uu____2156 msg
                | FStar_Errors.Error (uu____2164,msg,uu____2166) ->
                    let uu____2167 = tts e1 t  in
                    let uu____2168 =
                      let uu____2169 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2169
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2167 uu____2168 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.Reify;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Simplify;
        FStar_TypeChecker_Env.UnfoldTac;
        FStar_TypeChecker_Env.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____2196  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___375_2214 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___375_2214.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___375_2214.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___375_2214.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___375_2214.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___375_2214.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___375_2214.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___375_2214.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___375_2214.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___375_2214.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___375_2214.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___375_2214.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___375_2214.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2238 = get_guard_policy ()  in
      bind uu____2238
        (fun old_pol  ->
           let uu____2244 = set_guard_policy pol  in
           bind uu____2244
             (fun uu____2248  ->
                bind t
                  (fun r  ->
                     let uu____2252 = set_guard_policy old_pol  in
                     bind uu____2252 (fun uu____2256  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2259 = let uu____2264 = cur_goal ()  in trytac uu____2264  in
  bind uu____2259
    (fun uu___346_2271  ->
       match uu___346_2271 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2277 = FStar_Options.peek ()  in ret uu____2277)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2299  ->
             let uu____2300 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2300)
          (fun uu____2303  ->
             let uu____2304 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2304
               (fun uu____2308  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2312 =
                         let uu____2313 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2313.FStar_TypeChecker_Env.guard_f  in
                       match uu____2312 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2317 = istrivial e f  in
                           if uu____2317
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2327 =
                                          let uu____2332 =
                                            let uu____2333 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2333
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2332)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2327);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2336  ->
                                           let uu____2337 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2337)
                                        (fun uu____2340  ->
                                           let uu____2341 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2341
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___376_2348 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___376_2348.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___376_2348.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___376_2348.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2351  ->
                                           let uu____2352 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2352)
                                        (fun uu____2355  ->
                                           let uu____2356 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2356
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___377_2363 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___377_2363.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___377_2363.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___377_2363.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2366  ->
                                           let uu____2367 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2367)
                                        (fun uu____2369  ->
                                           try
                                             (fun uu___379_2374  ->
                                                match () with
                                                | () ->
                                                    let uu____2377 =
                                                      let uu____2378 =
                                                        let uu____2379 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2379
                                                         in
                                                      Prims.op_Negation
                                                        uu____2378
                                                       in
                                                    if uu____2377
                                                    then
                                                      mlog
                                                        (fun uu____2384  ->
                                                           let uu____2385 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2385)
                                                        (fun uu____2387  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___378_2390 ->
                                               mlog
                                                 (fun uu____2395  ->
                                                    let uu____2396 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2396)
                                                 (fun uu____2398  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2408 =
      let uu____2411 = cur_goal ()  in
      bind uu____2411
        (fun goal  ->
           let uu____2417 =
             let uu____2426 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2426 t  in
           bind uu____2417
             (fun uu____2437  ->
                match uu____2437 with
                | (uu____2446,typ,uu____2448) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2408
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2477 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2477 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2488  ->
    let uu____2491 = cur_goal ()  in
    bind uu____2491
      (fun goal  ->
         let uu____2497 =
           let uu____2498 = FStar_Tactics_Types.goal_env goal  in
           let uu____2499 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2498 uu____2499  in
         if uu____2497
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2503 =
              let uu____2504 = FStar_Tactics_Types.goal_env goal  in
              let uu____2505 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2504 uu____2505  in
            fail1 "Not a trivial goal: %s" uu____2503))
  
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
          let uu____2534 =
            let uu____2535 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2535.FStar_TypeChecker_Env.guard_f  in
          match uu____2534 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2543 = istrivial e f  in
              if uu____2543
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2551 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2551
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___380_2561 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___380_2561.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___380_2561.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___380_2561.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2568  ->
    let uu____2571 = cur_goal ()  in
    bind uu____2571
      (fun g  ->
         let uu____2577 = is_irrelevant g  in
         if uu____2577
         then bind __dismiss (fun uu____2581  -> add_smt_goals [g])
         else
           (let uu____2583 =
              let uu____2584 = FStar_Tactics_Types.goal_env g  in
              let uu____2585 = FStar_Tactics_Types.goal_type g  in
              tts uu____2584 uu____2585  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2583))
  
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
             let uu____2634 =
               try
                 (fun uu___385_2657  ->
                    match () with
                    | () ->
                        let uu____2668 =
                          let uu____2677 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2677
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2668) ()
               with | uu___384_2687 -> fail "divide: not enough goals"  in
             bind uu____2634
               (fun uu____2723  ->
                  match uu____2723 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___381_2749 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___381_2749.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___381_2749.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___381_2749.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___381_2749.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___381_2749.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___381_2749.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___381_2749.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___381_2749.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___381_2749.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___381_2749.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___381_2749.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2750 = set lp  in
                      bind uu____2750
                        (fun uu____2758  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___382_2774 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___382_2774.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___382_2774.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___382_2774.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___382_2774.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___382_2774.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___382_2774.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___382_2774.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___382_2774.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___382_2774.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___382_2774.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___382_2774.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2775 = set rp  in
                                     bind uu____2775
                                       (fun uu____2783  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___383_2799 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___383_2799.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___383_2799.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2800 = set p'
                                                       in
                                                    bind uu____2800
                                                      (fun uu____2808  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2814 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2835 = divide FStar_BigInt.one f idtac  in
    bind uu____2835
      (fun uu____2848  -> match uu____2848 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2885::uu____2886 ->
             let uu____2889 =
               let uu____2898 = map tau  in
               divide FStar_BigInt.one tau uu____2898  in
             bind uu____2889
               (fun uu____2916  ->
                  match uu____2916 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2957 =
        bind t1
          (fun uu____2962  ->
             let uu____2963 = map t2  in
             bind uu____2963 (fun uu____2971  -> ret ()))
         in
      focus uu____2957
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2980  ->
    let uu____2983 =
      let uu____2986 = cur_goal ()  in
      bind uu____2986
        (fun goal  ->
           let uu____2995 =
             let uu____3002 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3002  in
           match uu____2995 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3011 =
                 let uu____3012 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3012  in
               if uu____3011
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3017 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3017 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3031 = new_uvar "intro" env' typ'  in
                  bind uu____3031
                    (fun uu____3047  ->
                       match uu____3047 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3071 = set_solution goal sol  in
                           bind uu____3071
                             (fun uu____3077  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3079 =
                                  let uu____3082 = bnorm_goal g  in
                                  replace_cur uu____3082  in
                                bind uu____3079 (fun uu____3084  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3089 =
                 let uu____3090 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3091 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3090 uu____3091  in
               fail1 "goal is not an arrow (%s)" uu____3089)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2983
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3106  ->
    let uu____3113 = cur_goal ()  in
    bind uu____3113
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3130 =
            let uu____3137 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3137  in
          match uu____3130 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3150 =
                let uu____3151 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3151  in
              if uu____3150
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3164 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3164
                    in
                 let bs =
                   let uu____3174 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3174; b]  in
                 let env' =
                   let uu____3200 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3200 bs  in
                 let uu____3201 =
                   let uu____3208 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3208  in
                 bind uu____3201
                   (fun uu____3227  ->
                      match uu____3227 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3241 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3244 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3241
                              FStar_Parser_Const.effect_Tot_lid uu____3244 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3262 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3262 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3284 =
                                   let uu____3285 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3285.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3284
                                  in
                               let uu____3298 = set_solution goal tm  in
                               bind uu____3298
                                 (fun uu____3307  ->
                                    let uu____3308 =
                                      let uu____3311 =
                                        bnorm_goal
                                          (let uu___386_3314 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___386_3314.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___386_3314.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___386_3314.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3311  in
                                    bind uu____3308
                                      (fun uu____3321  ->
                                         let uu____3322 =
                                           let uu____3327 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3327, b)  in
                                         ret uu____3322)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3336 =
                let uu____3337 = FStar_Tactics_Types.goal_env goal  in
                let uu____3338 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3337 uu____3338  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3336))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3356 = cur_goal ()  in
    bind uu____3356
      (fun goal  ->
         mlog
           (fun uu____3363  ->
              let uu____3364 =
                let uu____3365 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3365  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3364)
           (fun uu____3370  ->
              let steps =
                let uu____3374 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3374
                 in
              let t =
                let uu____3378 = FStar_Tactics_Types.goal_env goal  in
                let uu____3379 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3378 uu____3379  in
              let uu____3380 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3380))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3404 =
          mlog
            (fun uu____3409  ->
               let uu____3410 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3410)
            (fun uu____3412  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3418 -> g.FStar_Tactics_Types.opts
                      | uu____3421 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3426  ->
                         let uu____3427 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3427)
                      (fun uu____3430  ->
                         let uu____3431 = __tc e t  in
                         bind uu____3431
                           (fun uu____3452  ->
                              match uu____3452 with
                              | (t1,uu____3462,uu____3463) ->
                                  let steps =
                                    let uu____3467 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3467
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3404
  
let (refine_intro : unit -> unit tac) =
  fun uu____3481  ->
    let uu____3484 =
      let uu____3487 = cur_goal ()  in
      bind uu____3487
        (fun g  ->
           let uu____3494 =
             let uu____3505 = FStar_Tactics_Types.goal_env g  in
             let uu____3506 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3505 uu____3506
              in
           match uu____3494 with
           | (uu____3509,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3534 =
                 let uu____3539 =
                   let uu____3544 =
                     let uu____3545 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3545]  in
                   FStar_Syntax_Subst.open_term uu____3544 phi  in
                 match uu____3539 with
                 | (bvs,phi1) ->
                     let uu____3570 =
                       let uu____3571 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3571  in
                     (uu____3570, phi1)
                  in
               (match uu____3534 with
                | (bv1,phi1) ->
                    let uu____3590 =
                      let uu____3593 = FStar_Tactics_Types.goal_env g  in
                      let uu____3594 =
                        let uu____3595 =
                          let uu____3598 =
                            let uu____3599 =
                              let uu____3606 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3606)  in
                            FStar_Syntax_Syntax.NT uu____3599  in
                          [uu____3598]  in
                        FStar_Syntax_Subst.subst uu____3595 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3593
                        uu____3594 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3590
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3614  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3484
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3633 = cur_goal ()  in
      bind uu____3633
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3641 = FStar_Tactics_Types.goal_env goal  in
               let uu____3642 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3641 uu____3642
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3644 = __tc env t  in
           bind uu____3644
             (fun uu____3663  ->
                match uu____3663 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3678  ->
                         let uu____3679 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3680 =
                           let uu____3681 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3681
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3679 uu____3680)
                      (fun uu____3684  ->
                         let uu____3685 =
                           let uu____3688 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3688 guard  in
                         bind uu____3685
                           (fun uu____3690  ->
                              mlog
                                (fun uu____3694  ->
                                   let uu____3695 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3696 =
                                     let uu____3697 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3697
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3695 uu____3696)
                                (fun uu____3700  ->
                                   let uu____3701 =
                                     let uu____3704 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3705 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3704 typ uu____3705  in
                                   bind uu____3701
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3711 =
                                             let uu____3712 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3712 t1  in
                                           let uu____3713 =
                                             let uu____3714 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3714 typ  in
                                           let uu____3715 =
                                             let uu____3716 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3717 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3716 uu____3717  in
                                           let uu____3718 =
                                             let uu____3719 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3720 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3719 uu____3720  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3711 uu____3713 uu____3715
                                             uu____3718)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3740 =
          mlog
            (fun uu____3745  ->
               let uu____3746 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3746)
            (fun uu____3749  ->
               let uu____3750 =
                 let uu____3757 = __exact_now set_expected_typ1 tm  in
                 catch uu____3757  in
               bind uu____3750
                 (fun uu___348_3766  ->
                    match uu___348_3766 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3777  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3780  ->
                             let uu____3781 =
                               let uu____3788 =
                                 let uu____3791 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3791
                                   (fun uu____3796  ->
                                      let uu____3797 = refine_intro ()  in
                                      bind uu____3797
                                        (fun uu____3801  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3788  in
                             bind uu____3781
                               (fun uu___347_3808  ->
                                  match uu___347_3808 with
                                  | FStar_Util.Inr r -> ret ()
                                  | FStar_Util.Inl uu____3816 -> fail e))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3740
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3866 = f x  in
          bind uu____3866
            (fun y  ->
               let uu____3874 = mapM f xs  in
               bind uu____3874 (fun ys  -> ret (y :: ys)))
  
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
    FStar_Pervasives_Native.tuple3 Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
            FStar_Pervasives_Native.tuple3 Prims.list tac)
  =
  fun acc  ->
    fun e  ->
      fun ty1  ->
        fun ty2  ->
          let uu____3945 = do_unify e ty1 ty2  in
          bind uu____3945
            (fun uu___349_3957  ->
               if uu___349_3957
               then ret acc
               else
                 (let uu____3976 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3976 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3997 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3998 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3997
                        uu____3998
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4013 =
                        let uu____4014 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4014  in
                      if uu____4013
                      then fail "Codomain is effectful"
                      else
                        (let uu____4034 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4034
                           (fun uu____4060  ->
                              match uu____4060 with
                              | (uvt,uv) ->
                                  let typ = comp_to_typ c  in
                                  let typ' =
                                    FStar_Syntax_Subst.subst
                                      [FStar_Syntax_Syntax.NT
                                         ((FStar_Pervasives_Native.fst b),
                                           uvt)] typ
                                     in
                                  __try_match_by_application
                                    ((uvt, (FStar_Pervasives_Native.snd b),
                                       uv) :: acc) e typ' ty2))))
  
let (try_match_by_application :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Syntax_Syntax.ctx_uvar)
          FStar_Pervasives_Native.tuple3 Prims.list tac)
  = fun e  -> fun ty1  -> fun ty2  -> __try_match_by_application [] e ty1 ty2 
let (t_apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4146 =
        mlog
          (fun uu____4151  ->
             let uu____4152 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4152)
          (fun uu____4155  ->
             let uu____4156 = cur_goal ()  in
             bind uu____4156
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4164 = __tc e tm  in
                  bind uu____4164
                    (fun uu____4185  ->
                       match uu____4185 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4198 =
                             let uu____4209 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4209  in
                           bind uu____4198
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4252  ->
                                       fun w  ->
                                         match uu____4252 with
                                         | (uvt,q,uu____4270) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4302 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4319  ->
                                       fun s  ->
                                         match uu____4319 with
                                         | (uu____4331,uu____4332,uv) ->
                                             let uu____4334 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4334) uvs uu____4302
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4343 = solve' goal w  in
                                bind uu____4343
                                  (fun uu____4348  ->
                                     let uu____4349 =
                                       mapM
                                         (fun uu____4366  ->
                                            match uu____4366 with
                                            | (uvt,q,uv) ->
                                                let uu____4378 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4378 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4383 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4384 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4384
                                                     then ret ()
                                                     else
                                                       (let uu____4388 =
                                                          let uu____4391 =
                                                            bnorm_goal
                                                              (let uu___387_4394
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___387_4394.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___387_4394.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4391]  in
                                                        add_goals uu____4388)))
                                         uvs
                                        in
                                     bind uu____4349
                                       (fun uu____4398  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4146
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4423 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4423
    then
      let uu____4430 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4445 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4498 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4430 with
      | (pre,post) ->
          let post1 =
            let uu____4530 =
              let uu____4541 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4541]  in
            FStar_Syntax_Util.mk_app post uu____4530  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4571 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4571
       then
         let uu____4578 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4578
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4611 =
      let uu____4614 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4621  ->
                  let uu____4622 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4622)
               (fun uu____4626  ->
                  let is_unit_t t =
                    let uu____4633 =
                      let uu____4634 = FStar_Syntax_Subst.compress t  in
                      uu____4634.FStar_Syntax_Syntax.n  in
                    match uu____4633 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4638 -> false  in
                  let uu____4639 = cur_goal ()  in
                  bind uu____4639
                    (fun goal  ->
                       let uu____4645 =
                         let uu____4654 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4654 tm  in
                       bind uu____4645
                         (fun uu____4669  ->
                            match uu____4669 with
                            | (tm1,t,guard) ->
                                let uu____4681 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4681 with
                                 | (bs,comp) ->
                                     let uu____4714 = lemma_or_sq comp  in
                                     (match uu____4714 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4733 =
                                            FStar_List.fold_left
                                              (fun uu____4781  ->
                                                 fun uu____4782  ->
                                                   match (uu____4781,
                                                           uu____4782)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4895 =
                                                         is_unit_t b_t  in
                                                       if uu____4895
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4933 =
                                                            let uu____4946 =
                                                              let uu____4947
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____4947.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____4950 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____4946
                                                              uu____4950 b_t
                                                             in
                                                          match uu____4933
                                                          with
                                                          | (u,uu____4968,g_u)
                                                              ->
                                                              let uu____4982
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4982,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4733 with
                                           | (uvs,implicits,subst1) ->
                                               let uvs1 = FStar_List.rev uvs
                                                  in
                                               let pre1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 pre
                                                  in
                                               let post1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 post
                                                  in
                                               let uu____5061 =
                                                 let uu____5064 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5065 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5066 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5064
                                                   uu____5065 uu____5066
                                                  in
                                               bind uu____5061
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5074 =
                                                        let uu____5075 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5075 tm1
                                                         in
                                                      let uu____5076 =
                                                        let uu____5077 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5078 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5077
                                                          uu____5078
                                                         in
                                                      let uu____5079 =
                                                        let uu____5080 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5081 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5080
                                                          uu____5081
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5074 uu____5076
                                                        uu____5079
                                                    else
                                                      (let uu____5083 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5083
                                                         (fun uu____5088  ->
                                                            let uu____5089 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5089
                                                              (fun uu____5097
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5122
                                                                    =
                                                                    let uu____5125
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5125
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5122
                                                                     in
                                                                   FStar_List.existsML
                                                                    (fun u 
                                                                    ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                    in
                                                                 let appears
                                                                   uv goals =
                                                                   FStar_List.existsML
                                                                    (fun g' 
                                                                    ->
                                                                    let uu____5160
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5160)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5176
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5176
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5194)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5220)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5237
                                                                    -> false)
                                                                    in
                                                                 let uu____5238
                                                                   =
                                                                   FStar_All.pipe_right
                                                                    implicits.FStar_TypeChecker_Env.implicits
                                                                    (mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let term
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_tm
                                                                     in
                                                                    let ctx_uvar
                                                                    =
                                                                    imp.FStar_TypeChecker_Env.imp_uvar
                                                                     in
                                                                    let uu____5268
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5268
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5290)
                                                                    ->
                                                                    let uu____5315
                                                                    =
                                                                    let uu____5316
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5316.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5315
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5324)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___388_5344
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___388_5344.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___388_5344.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___388_5344.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5347
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5353
                                                                     ->
                                                                    let uu____5354
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5355
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5354
                                                                    uu____5355)
                                                                    (fun
                                                                    uu____5360
                                                                     ->
                                                                    let env =
                                                                    let uu___389_5362
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___389_5362.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5364
                                                                    =
                                                                    let uu____5367
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5368
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5369
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5368
                                                                    uu____5369
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5371
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5367
                                                                    uu____5371
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5364
                                                                    (fun
                                                                    uu____5375
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5238
                                                                   (fun
                                                                    sub_goals
                                                                     ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_List.flatten
                                                                    sub_goals
                                                                     in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu____5437
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5437
                                                                    then
                                                                    let uu____5440
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5440
                                                                    else
                                                                    filter' f
                                                                    xs1  in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5454
                                                                    =
                                                                    let uu____5455
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5455
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5454)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5456
                                                                    =
                                                                    let uu____5459
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5459
                                                                    guard  in
                                                                    bind
                                                                    uu____5456
                                                                    (fun
                                                                    uu____5462
                                                                     ->
                                                                    let uu____5463
                                                                    =
                                                                    let uu____5466
                                                                    =
                                                                    let uu____5467
                                                                    =
                                                                    let uu____5468
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5469
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5468
                                                                    uu____5469
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5467
                                                                     in
                                                                    if
                                                                    uu____5466
                                                                    then
                                                                    let uu____5472
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5472
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5463
                                                                    (fun
                                                                    uu____5475
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4614  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4611
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5497 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5497 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5507::(e1,uu____5509)::(e2,uu____5511)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5572 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5596 = destruct_eq' typ  in
    match uu____5596 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5626 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5626 with
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
        let uu____5688 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5688 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5736 = aux e'  in
               FStar_Util.map_opt uu____5736
                 (fun uu____5760  ->
                    match uu____5760 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5781 = aux e  in
      FStar_Util.map_opt uu____5781
        (fun uu____5805  ->
           match uu____5805 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5872 =
            let uu____5881 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5881  in
          FStar_Util.map_opt uu____5872
            (fun uu____5896  ->
               match uu____5896 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___390_5915 = bv  in
                     let uu____5916 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___390_5915.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___390_5915.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5916
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___391_5924 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5925 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5934 =
                       let uu____5937 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5937  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___391_5924.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5925;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5934;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___391_5924.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___391_5924.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___391_5924.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___392_5938 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___392_5938.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___392_5938.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___392_5938.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5948 =
      let uu____5951 = cur_goal ()  in
      bind uu____5951
        (fun goal  ->
           let uu____5959 = h  in
           match uu____5959 with
           | (bv,uu____5963) ->
               mlog
                 (fun uu____5971  ->
                    let uu____5972 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5973 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5972
                      uu____5973)
                 (fun uu____5976  ->
                    let uu____5977 =
                      let uu____5986 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5986  in
                    match uu____5977 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6007 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6007 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6022 =
                               let uu____6023 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6023.FStar_Syntax_Syntax.n  in
                             (match uu____6022 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___393_6040 = bv1  in
                                    let uu____6041 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___393_6040.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___393_6040.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6041
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___394_6049 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6050 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6059 =
                                      let uu____6062 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6062
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___394_6049.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6050;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6059;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___394_6049.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___394_6049.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___394_6049.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___395_6065 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___395_6065.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___395_6065.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___395_6065.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6066 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6067 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5948
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6092 =
        let uu____6095 = cur_goal ()  in
        bind uu____6095
          (fun goal  ->
             let uu____6106 = b  in
             match uu____6106 with
             | (bv,uu____6110) ->
                 let bv' =
                   let uu____6116 =
                     let uu___396_6117 = bv  in
                     let uu____6118 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6118;
                       FStar_Syntax_Syntax.index =
                         (uu___396_6117.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___396_6117.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6116  in
                 let s1 =
                   let uu____6122 =
                     let uu____6123 =
                       let uu____6130 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6130)  in
                     FStar_Syntax_Syntax.NT uu____6123  in
                   [uu____6122]  in
                 let uu____6135 = subst_goal bv bv' s1 goal  in
                 (match uu____6135 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6092
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6154 =
      let uu____6157 = cur_goal ()  in
      bind uu____6157
        (fun goal  ->
           let uu____6166 = b  in
           match uu____6166 with
           | (bv,uu____6170) ->
               let uu____6175 =
                 let uu____6184 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6184  in
               (match uu____6175 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6205 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6205 with
                     | (ty,u) ->
                         let uu____6214 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6214
                           (fun uu____6232  ->
                              match uu____6232 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___397_6242 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___397_6242.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___397_6242.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6246 =
                                      let uu____6247 =
                                        let uu____6254 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6254)  in
                                      FStar_Syntax_Syntax.NT uu____6247  in
                                    [uu____6246]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___398_6266 = b1  in
                                         let uu____6267 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___398_6266.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___398_6266.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6267
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6274  ->
                                       let new_goal =
                                         let uu____6276 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6277 =
                                           let uu____6278 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6278
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6276 uu____6277
                                          in
                                       let uu____6279 = add_goals [new_goal]
                                          in
                                       bind uu____6279
                                         (fun uu____6284  ->
                                            let uu____6285 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6285
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6154
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6308 =
        let uu____6311 = cur_goal ()  in
        bind uu____6311
          (fun goal  ->
             let uu____6320 = b  in
             match uu____6320 with
             | (bv,uu____6324) ->
                 let uu____6329 =
                   let uu____6338 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6338  in
                 (match uu____6329 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6362 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6362
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___399_6367 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___399_6367.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___399_6367.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6369 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6369))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6308
  
let (revert : unit -> unit tac) =
  fun uu____6380  ->
    let uu____6383 = cur_goal ()  in
    bind uu____6383
      (fun goal  ->
         let uu____6389 =
           let uu____6396 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6396  in
         match uu____6389 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6412 =
                 let uu____6415 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6415  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6412
                in
             let uu____6430 = new_uvar "revert" env' typ'  in
             bind uu____6430
               (fun uu____6445  ->
                  match uu____6445 with
                  | (r,u_r) ->
                      let uu____6454 =
                        let uu____6457 =
                          let uu____6458 =
                            let uu____6459 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6459.FStar_Syntax_Syntax.pos  in
                          let uu____6462 =
                            let uu____6467 =
                              let uu____6468 =
                                let uu____6477 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6477  in
                              [uu____6468]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6467  in
                          uu____6462 FStar_Pervasives_Native.None uu____6458
                           in
                        set_solution goal uu____6457  in
                      bind uu____6454
                        (fun uu____6498  ->
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
      let uu____6510 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6510
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6525 = cur_goal ()  in
    bind uu____6525
      (fun goal  ->
         mlog
           (fun uu____6533  ->
              let uu____6534 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6535 =
                let uu____6536 =
                  let uu____6537 =
                    let uu____6546 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6546  in
                  FStar_All.pipe_right uu____6537 FStar_List.length  in
                FStar_All.pipe_right uu____6536 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6534 uu____6535)
           (fun uu____6563  ->
              let uu____6564 =
                let uu____6573 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6573  in
              match uu____6564 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6612 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6612
                        then
                          let uu____6615 =
                            let uu____6616 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6616
                             in
                          fail uu____6615
                        else check1 bvs2
                     in
                  let uu____6618 =
                    let uu____6619 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6619  in
                  if uu____6618
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6623 = check1 bvs  in
                     bind uu____6623
                       (fun uu____6629  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6631 =
                            let uu____6638 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6638  in
                          bind uu____6631
                            (fun uu____6647  ->
                               match uu____6647 with
                               | (ut,uvar_ut) ->
                                   let uu____6656 = set_solution goal ut  in
                                   bind uu____6656
                                     (fun uu____6661  ->
                                        let uu____6662 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6662))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6669  ->
    let uu____6672 = cur_goal ()  in
    bind uu____6672
      (fun goal  ->
         let uu____6678 =
           let uu____6685 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6685  in
         match uu____6678 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6693) ->
             let uu____6698 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6698)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6708 = cur_goal ()  in
    bind uu____6708
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6718 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6718  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6721  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6731 = cur_goal ()  in
    bind uu____6731
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6741 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6741  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6744  -> add_goals [g']))
  
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
            let uu____6784 = FStar_Syntax_Subst.compress t  in
            uu____6784.FStar_Syntax_Syntax.n  in
          let uu____6787 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___403_6793 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___403_6793.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___403_6793.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6787
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6809 =
                   let uu____6810 = FStar_Syntax_Subst.compress t1  in
                   uu____6810.FStar_Syntax_Syntax.n  in
                 match uu____6809 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6841 = ff hd1  in
                     bind uu____6841
                       (fun hd2  ->
                          let fa uu____6867 =
                            match uu____6867 with
                            | (a,q) ->
                                let uu____6888 = ff a  in
                                bind uu____6888 (fun a1  -> ret (a1, q))
                             in
                          let uu____6907 = mapM fa args  in
                          bind uu____6907
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6989 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6989 with
                      | (bs1,t') ->
                          let uu____6998 =
                            let uu____7001 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7001 t'  in
                          bind uu____6998
                            (fun t''  ->
                               let uu____7005 =
                                 let uu____7006 =
                                   let uu____7025 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7034 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7025, uu____7034, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7006  in
                               ret uu____7005))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7109 = ff hd1  in
                     bind uu____7109
                       (fun hd2  ->
                          let ffb br =
                            let uu____7124 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7124 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7156 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7156  in
                                let uu____7157 = ff1 e  in
                                bind uu____7157
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7172 = mapM ffb brs  in
                          bind uu____7172
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7216;
                          FStar_Syntax_Syntax.lbtyp = uu____7217;
                          FStar_Syntax_Syntax.lbeff = uu____7218;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7220;
                          FStar_Syntax_Syntax.lbpos = uu____7221;_}::[]),e)
                     ->
                     let lb =
                       let uu____7246 =
                         let uu____7247 = FStar_Syntax_Subst.compress t1  in
                         uu____7247.FStar_Syntax_Syntax.n  in
                       match uu____7246 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7251) -> lb
                       | uu____7264 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7273 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7273
                         (fun def1  ->
                            ret
                              (let uu___400_7279 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___400_7279.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___400_7279.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___400_7279.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___400_7279.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___400_7279.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___400_7279.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7280 = fflb lb  in
                     bind uu____7280
                       (fun lb1  ->
                          let uu____7290 =
                            let uu____7295 =
                              let uu____7296 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7296]  in
                            FStar_Syntax_Subst.open_term uu____7295 e  in
                          match uu____7290 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7326 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7326  in
                              let uu____7327 = ff1 e1  in
                              bind uu____7327
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7368 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7368
                         (fun def  ->
                            ret
                              (let uu___401_7374 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___401_7374.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___401_7374.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___401_7374.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___401_7374.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___401_7374.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___401_7374.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7375 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7375 with
                      | (lbs1,e1) ->
                          let uu____7390 = mapM fflb lbs1  in
                          bind uu____7390
                            (fun lbs2  ->
                               let uu____7402 = ff e1  in
                               bind uu____7402
                                 (fun e2  ->
                                    let uu____7410 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7410 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7478 = ff t2  in
                     bind uu____7478
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7509 = ff t2  in
                     bind uu____7509
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7516 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___402_7523 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___402_7523.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___402_7523.FStar_Syntax_Syntax.vars)
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
            let uu____7560 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___404_7569 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___404_7569.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___404_7569.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___404_7569.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___404_7569.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___404_7569.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___404_7569.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___404_7569.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___404_7569.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___404_7569.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___404_7569.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___404_7569.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___404_7569.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___404_7569.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___404_7569.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___404_7569.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___404_7569.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___404_7569.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___404_7569.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___404_7569.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___404_7569.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___404_7569.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___404_7569.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___404_7569.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___404_7569.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___404_7569.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___404_7569.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___404_7569.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___404_7569.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___404_7569.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___404_7569.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___404_7569.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___404_7569.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___404_7569.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___404_7569.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___404_7569.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___404_7569.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___404_7569.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___404_7569.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___404_7569.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___404_7569.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___404_7569.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7560 with
            | (t1,lcomp,g) ->
                let uu____7575 =
                  (let uu____7578 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7578) ||
                    (let uu____7580 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7580)
                   in
                if uu____7575
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7588 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7588
                       (fun uu____7604  ->
                          match uu____7604 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7617  ->
                                    let uu____7618 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7619 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7618 uu____7619);
                               (let uu____7620 =
                                  let uu____7623 =
                                    let uu____7624 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7624 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7623
                                    opts
                                   in
                                bind uu____7620
                                  (fun uu____7627  ->
                                     let uu____7628 =
                                       bind tau
                                         (fun uu____7634  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7640  ->
                                                 let uu____7641 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7642 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7641 uu____7642);
                                            ret ut1)
                                        in
                                     focus uu____7628))))
                      in
                   let uu____7643 = catch rewrite_eq  in
                   bind uu____7643
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
          let uu____7841 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7841
            (fun t1  ->
               let uu____7849 =
                 f env
                   (let uu___407_7858 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___407_7858.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___407_7858.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7849
                 (fun uu____7874  ->
                    match uu____7874 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7897 =
                               let uu____7898 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7898.FStar_Syntax_Syntax.n  in
                             match uu____7897 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7935 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7935
                                   (fun uu____7960  ->
                                      match uu____7960 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7976 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7976
                                            (fun uu____8003  ->
                                               match uu____8003 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___405_8033 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___405_8033.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___405_8033.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8075 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8075 with
                                  | (bs1,t') ->
                                      let uu____8090 =
                                        let uu____8097 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8097 ctrl1 t'
                                         in
                                      bind uu____8090
                                        (fun uu____8115  ->
                                           match uu____8115 with
                                           | (t'',ctrl2) ->
                                               let uu____8130 =
                                                 let uu____8137 =
                                                   let uu___406_8140 = t4  in
                                                   let uu____8143 =
                                                     let uu____8144 =
                                                       let uu____8163 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8172 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8163,
                                                         uu____8172, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8144
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8143;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___406_8140.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___406_8140.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8137, ctrl2)  in
                                               ret uu____8130))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8225 -> ret (t3, ctrl1))))

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
              let uu____8272 = ctrl_tac_fold f env ctrl t  in
              bind uu____8272
                (fun uu____8296  ->
                   match uu____8296 with
                   | (t1,ctrl1) ->
                       let uu____8311 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8311
                         (fun uu____8338  ->
                            match uu____8338 with
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
              let uu____8422 =
                let uu____8429 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8429
                  (fun uu____8438  ->
                     let uu____8439 = ctrl t1  in
                     bind uu____8439
                       (fun res  ->
                          let uu____8462 = trivial ()  in
                          bind uu____8462 (fun uu____8470  -> ret res)))
                 in
              bind uu____8422
                (fun uu____8486  ->
                   match uu____8486 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8510 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___408_8519 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___408_8519.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___408_8519.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___408_8519.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___408_8519.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___408_8519.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___408_8519.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___408_8519.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___408_8519.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___408_8519.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___408_8519.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___408_8519.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___408_8519.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___408_8519.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___408_8519.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___408_8519.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___408_8519.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___408_8519.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___408_8519.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___408_8519.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___408_8519.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___408_8519.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___408_8519.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___408_8519.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___408_8519.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___408_8519.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___408_8519.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___408_8519.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___408_8519.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___408_8519.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___408_8519.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___408_8519.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___408_8519.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___408_8519.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___408_8519.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___408_8519.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___408_8519.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___408_8519.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___408_8519.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___408_8519.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___408_8519.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___408_8519.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8510 with
                          | (t2,lcomp,g) ->
                              let uu____8529 =
                                (let uu____8532 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8532) ||
                                  (let uu____8534 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8534)
                                 in
                              if uu____8529
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8547 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8547
                                   (fun uu____8567  ->
                                      match uu____8567 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8584  ->
                                                let uu____8585 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8586 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8585 uu____8586);
                                           (let uu____8587 =
                                              let uu____8590 =
                                                let uu____8591 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8591 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8590 opts
                                               in
                                            bind uu____8587
                                              (fun uu____8598  ->
                                                 let uu____8599 =
                                                   bind rewriter
                                                     (fun uu____8613  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8619  ->
                                                             let uu____8620 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8621 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8620
                                                               uu____8621);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8599)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8662 =
        bind get
          (fun ps  ->
             let uu____8672 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8672 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8709  ->
                       let uu____8710 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8710);
                  bind dismiss_all
                    (fun uu____8713  ->
                       let uu____8714 =
                         let uu____8721 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8721
                           keepGoing gt1
                          in
                       bind uu____8714
                         (fun uu____8733  ->
                            match uu____8733 with
                            | (gt',uu____8741) ->
                                (log ps
                                   (fun uu____8745  ->
                                      let uu____8746 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8746);
                                 (let uu____8747 = push_goals gs  in
                                  bind uu____8747
                                    (fun uu____8752  ->
                                       let uu____8753 =
                                         let uu____8756 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8756]  in
                                       add_goals uu____8753)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8662
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8779 =
        bind get
          (fun ps  ->
             let uu____8789 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8789 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8826  ->
                       let uu____8827 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8827);
                  bind dismiss_all
                    (fun uu____8830  ->
                       let uu____8831 =
                         let uu____8834 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8834 gt1
                          in
                       bind uu____8831
                         (fun gt'  ->
                            log ps
                              (fun uu____8842  ->
                                 let uu____8843 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8843);
                            (let uu____8844 = push_goals gs  in
                             bind uu____8844
                               (fun uu____8849  ->
                                  let uu____8850 =
                                    let uu____8853 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8853]  in
                                  add_goals uu____8850))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8779
  
let (trefl : unit -> unit tac) =
  fun uu____8864  ->
    let uu____8867 =
      let uu____8870 = cur_goal ()  in
      bind uu____8870
        (fun g  ->
           let uu____8888 =
             let uu____8893 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8893  in
           match uu____8888 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8901 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8901 with
                | (hd1,args) ->
                    let uu____8940 =
                      let uu____8953 =
                        let uu____8954 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8954.FStar_Syntax_Syntax.n  in
                      (uu____8953, args)  in
                    (match uu____8940 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8968::(l,uu____8970)::(r,uu____8972)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9019 =
                           let uu____9022 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9022 l r  in
                         bind uu____9019
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9029 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9029 l
                                    in
                                 let r1 =
                                   let uu____9031 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9031 r
                                    in
                                 let uu____9032 =
                                   let uu____9035 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9035 l1 r1  in
                                 bind uu____9032
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9041 =
                                           let uu____9042 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9042 l1  in
                                         let uu____9043 =
                                           let uu____9044 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9044 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9041 uu____9043))))
                     | (hd2,uu____9046) ->
                         let uu____9063 =
                           let uu____9064 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9064 t  in
                         fail1 "trefl: not an equality (%s)" uu____9063))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8867
  
let (dup : unit -> unit tac) =
  fun uu____9077  ->
    let uu____9080 = cur_goal ()  in
    bind uu____9080
      (fun g  ->
         let uu____9086 =
           let uu____9093 = FStar_Tactics_Types.goal_env g  in
           let uu____9094 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9093 uu____9094  in
         bind uu____9086
           (fun uu____9103  ->
              match uu____9103 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___409_9113 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___409_9113.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___409_9113.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___409_9113.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9116  ->
                       let uu____9117 =
                         let uu____9120 = FStar_Tactics_Types.goal_env g  in
                         let uu____9121 =
                           let uu____9122 =
                             let uu____9123 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9124 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9123
                               uu____9124
                              in
                           let uu____9125 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9126 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9122 uu____9125 u
                             uu____9126
                            in
                         add_irrelevant_goal "dup equation" uu____9120
                           uu____9121 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9117
                         (fun uu____9129  ->
                            let uu____9130 = add_goals [g']  in
                            bind uu____9130 (fun uu____9134  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9141  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___410_9158 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___410_9158.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___410_9158.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___410_9158.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___410_9158.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___410_9158.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___410_9158.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___410_9158.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___410_9158.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___410_9158.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___410_9158.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___410_9158.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___410_9158.FStar_Tactics_Types.local_state)
                })
         | uu____9159 -> fail "flip: less than 2 goals")
  
let rec longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list ->
          ('a Prims.list,'a Prims.list,'a Prims.list)
            FStar_Pervasives_Native.tuple3
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs,y::ys) ->
              let uu____9284 = f x y  in
              if uu____9284 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9304 -> (acc, l11, l21)  in
        let uu____9319 = aux [] l1 l2  in
        match uu____9319 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal tac)
  =
  fun g1  ->
    fun g2  ->
      let close_forall_no_univs1 bs f =
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               FStar_Syntax_Util.mk_forall_no_univ
                 (FStar_Pervasives_Native.fst b) f1) bs f
         in
      let uu____9424 = get_phi g1  in
      match uu____9424 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9430 = get_phi g2  in
          (match uu____9430 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9442 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9442 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9473 =
                        FStar_TypeChecker_Env.binders_of_bindings r1  in
                      close_forall_no_univs1 uu____9473 phi1  in
                    let t2 =
                      let uu____9483 =
                        FStar_TypeChecker_Env.binders_of_bindings r2  in
                      close_forall_no_univs1 uu____9483 phi2  in
                    let uu____9492 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9492
                      (fun uu____9497  ->
                         let uu____9498 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9498
                           (fun uu____9505  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___411_9510 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9511 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___411_9510.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___411_9510.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___411_9510.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___411_9510.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9511;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___411_9510.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___411_9510.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___411_9510.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___411_9510.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___411_9510.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___411_9510.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___411_9510.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___411_9510.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___411_9510.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___411_9510.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___411_9510.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___411_9510.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___411_9510.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___411_9510.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___411_9510.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___411_9510.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___411_9510.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___411_9510.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___411_9510.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___411_9510.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___411_9510.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___411_9510.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___411_9510.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___411_9510.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___411_9510.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___411_9510.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___411_9510.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___411_9510.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___411_9510.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___411_9510.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___411_9510.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___411_9510.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___411_9510.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___411_9510.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___411_9510.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___411_9510.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9514 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9514
                                (fun goal  ->
                                   mlog
                                     (fun uu____9523  ->
                                        let uu____9524 =
                                          goal_to_string_verbose g1  in
                                        let uu____9525 =
                                          goal_to_string_verbose g2  in
                                        let uu____9526 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9524 uu____9525 uu____9526)
                                     (fun uu____9528  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9535  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9551 =
               set
                 (let uu___412_9556 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___412_9556.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___412_9556.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___412_9556.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___412_9556.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___412_9556.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___412_9556.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___412_9556.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___412_9556.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___412_9556.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___412_9556.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___412_9556.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___412_9556.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9551
               (fun uu____9559  ->
                  let uu____9560 = join_goals g1 g2  in
                  bind uu____9560 (fun g12  -> add_goals [g12]))
         | uu____9565 -> fail "join: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9574  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___413_9587 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___413_9587.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___413_9587.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___413_9587.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___413_9587.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___413_9587.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___413_9587.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___413_9587.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___413_9587.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___413_9587.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___413_9587.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___413_9587.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___413_9587.FStar_Tactics_Types.local_state)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9594  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9601 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9621 =
      let uu____9628 = cur_goal ()  in
      bind uu____9628
        (fun g  ->
           let uu____9638 =
             let uu____9647 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9647 t  in
           bind uu____9638
             (fun uu____9675  ->
                match uu____9675 with
                | (t1,typ,guard) ->
                    let uu____9691 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9691 with
                     | (hd1,args) ->
                         let uu____9740 =
                           let uu____9755 =
                             let uu____9756 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9756.FStar_Syntax_Syntax.n  in
                           (uu____9755, args)  in
                         (match uu____9740 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9777)::(q,uu____9779)::[]) when
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
                                let uu____9833 =
                                  let uu____9834 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9834
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9833
                                 in
                              let g2 =
                                let uu____9836 =
                                  let uu____9837 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9837
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9836
                                 in
                              bind __dismiss
                                (fun uu____9844  ->
                                   let uu____9845 = add_goals [g1; g2]  in
                                   bind uu____9845
                                     (fun uu____9854  ->
                                        let uu____9855 =
                                          let uu____9860 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9861 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9860, uu____9861)  in
                                        ret uu____9855))
                          | uu____9866 ->
                              let uu____9881 =
                                let uu____9882 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9882 typ  in
                              fail1 "Not a disjunction: %s" uu____9881))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9621
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9912 =
      let uu____9915 = cur_goal ()  in
      bind uu____9915
        (fun g  ->
           FStar_Options.push ();
           (let uu____9928 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9928);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___414_9935 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___414_9935.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___414_9935.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___414_9935.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9912
  
let (top_env : unit -> env tac) =
  fun uu____9947  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9960  ->
    let uu____9963 = cur_goal ()  in
    bind uu____9963
      (fun g  ->
         let uu____9969 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9969)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9978  ->
    let uu____9981 = cur_goal ()  in
    bind uu____9981
      (fun g  ->
         let uu____9987 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9987)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9996  ->
    let uu____9999 = cur_goal ()  in
    bind uu____9999
      (fun g  ->
         let uu____10005 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____10005)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10014  ->
    let uu____10017 = cur_env ()  in
    bind uu____10017
      (fun e  ->
         let uu____10023 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____10023)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10038 =
        mlog
          (fun uu____10043  ->
             let uu____10044 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10044)
          (fun uu____10047  ->
             let uu____10048 = cur_goal ()  in
             bind uu____10048
               (fun goal  ->
                  let env =
                    let uu____10056 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10056 ty  in
                  let uu____10057 = __tc env tm  in
                  bind uu____10057
                    (fun uu____10076  ->
                       match uu____10076 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10090  ->
                                let uu____10091 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10091)
                             (fun uu____10093  ->
                                mlog
                                  (fun uu____10096  ->
                                     let uu____10097 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10097)
                                  (fun uu____10100  ->
                                     let uu____10101 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10101
                                       (fun uu____10105  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10038
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10128 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10134 =
              let uu____10141 =
                let uu____10142 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10142
                 in
              new_uvar "uvar_env.2" env uu____10141  in
            bind uu____10134
              (fun uu____10158  ->
                 match uu____10158 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10128
        (fun typ  ->
           let uu____10170 = new_uvar "uvar_env" env typ  in
           bind uu____10170
             (fun uu____10184  ->
                match uu____10184 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10202 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10221 -> g.FStar_Tactics_Types.opts
             | uu____10224 -> FStar_Options.peek ()  in
           let uu____10227 = FStar_Syntax_Util.head_and_args t  in
           match uu____10227 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10247);
                FStar_Syntax_Syntax.pos = uu____10248;
                FStar_Syntax_Syntax.vars = uu____10249;_},uu____10250)
               ->
               let env1 =
                 let uu___415_10292 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___415_10292.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___415_10292.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___415_10292.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___415_10292.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___415_10292.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___415_10292.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___415_10292.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___415_10292.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___415_10292.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___415_10292.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___415_10292.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___415_10292.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___415_10292.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___415_10292.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___415_10292.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___415_10292.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___415_10292.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___415_10292.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___415_10292.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___415_10292.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___415_10292.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___415_10292.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___415_10292.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___415_10292.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___415_10292.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___415_10292.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___415_10292.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___415_10292.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___415_10292.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___415_10292.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___415_10292.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___415_10292.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___415_10292.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___415_10292.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___415_10292.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___415_10292.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___415_10292.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___415_10292.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___415_10292.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___415_10292.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___415_10292.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10294 =
                 let uu____10297 = bnorm_goal g  in [uu____10297]  in
               add_goals uu____10294
           | uu____10298 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10202
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10347 = if b then t2 else ret false  in
             bind uu____10347 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10358 = trytac comp  in
      bind uu____10358
        (fun uu___350_10366  ->
           match uu___350_10366 with
           | FStar_Pervasives_Native.Some (true ) -> ret true
           | FStar_Pervasives_Native.Some (false ) -> failwith "impossible"
           | FStar_Pervasives_Native.None  -> ret false)
  
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun e  ->
    fun t1  ->
      fun t2  ->
        let uu____10392 =
          bind get
            (fun ps  ->
               let uu____10398 = __tc e t1  in
               bind uu____10398
                 (fun uu____10418  ->
                    match uu____10418 with
                    | (t11,ty1,g1) ->
                        let uu____10430 = __tc e t2  in
                        bind uu____10430
                          (fun uu____10450  ->
                             match uu____10450 with
                             | (t21,ty2,g2) ->
                                 let uu____10462 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10462
                                   (fun uu____10467  ->
                                      let uu____10468 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10468
                                        (fun uu____10474  ->
                                           let uu____10475 =
                                             do_unify e ty1 ty2  in
                                           let uu____10478 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10475 uu____10478)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10392
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10511  ->
             let uu____10512 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10512
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
        (fun uu____10533  ->
           let uu____10534 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10534)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10544 =
      mlog
        (fun uu____10549  ->
           let uu____10550 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10550)
        (fun uu____10553  ->
           let uu____10554 = cur_goal ()  in
           bind uu____10554
             (fun g  ->
                let uu____10560 =
                  let uu____10569 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10569 ty  in
                bind uu____10560
                  (fun uu____10581  ->
                     match uu____10581 with
                     | (ty1,uu____10591,guard) ->
                         let uu____10593 =
                           let uu____10596 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10596 guard  in
                         bind uu____10593
                           (fun uu____10599  ->
                              let uu____10600 =
                                let uu____10603 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10604 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10603 uu____10604 ty1  in
                              bind uu____10600
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10610 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10610
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10616 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10617 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10616
                                          uu____10617
                                         in
                                      let nty =
                                        let uu____10619 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10619 ty1  in
                                      let uu____10620 =
                                        let uu____10623 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10623 ng nty  in
                                      bind uu____10620
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10629 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10629
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10544
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10692 =
      let uu____10701 = cur_goal ()  in
      bind uu____10701
        (fun g  ->
           let uu____10713 =
             let uu____10722 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10722 s_tm  in
           bind uu____10713
             (fun uu____10740  ->
                match uu____10740 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10758 =
                      let uu____10761 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10761 guard  in
                    bind uu____10758
                      (fun uu____10773  ->
                         let uu____10774 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10774 with
                         | (h,args) ->
                             let uu____10819 =
                               let uu____10826 =
                                 let uu____10827 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10827.FStar_Syntax_Syntax.n  in
                               match uu____10826 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10842;
                                      FStar_Syntax_Syntax.vars = uu____10843;_},us)
                                   -> ret (fv, us)
                               | uu____10853 -> fail "type is not an fv"  in
                             bind uu____10819
                               (fun uu____10873  ->
                                  match uu____10873 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10889 =
                                        let uu____10892 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10892 t_lid
                                         in
                                      (match uu____10889 with
                                       | FStar_Pervasives_Native.None  ->
                                           fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                (_lid,t_us,t_ps,t_ty,mut,c_lids)
                                                ->
                                                failwhen
                                                  ((FStar_List.length a_us)
                                                     <>
                                                     (FStar_List.length t_us))
                                                  "t_us don't match?"
                                                  (fun uu____10941  ->
                                                     let uu____10942 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10942 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10957 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10985
                                                                  =
                                                                  let uu____10988
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10988
                                                                    c_lid
                                                                   in
                                                                match uu____10985
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                     ->
                                                                    fail
                                                                    "ctor not found?"
                                                                | FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (
                                                                    match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    (_c_lid,c_us,c_ty,_t_lid,nparam,mut1)
                                                                    ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor)
                                                                     in
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_us) <>
                                                                    (FStar_List.length
                                                                    c_us))
                                                                    "t_us don't match?"
                                                                    (fun
                                                                    uu____11058
                                                                     ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us
                                                                     in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty
                                                                     in
                                                                    let uu____11063
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11063
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11086
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11086
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11129
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11129
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11202
                                                                    =
                                                                    let uu____11203
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11203
                                                                     in
                                                                    failwhen
                                                                    uu____11202
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11220
                                                                     ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    }  in
                                                                    let is_imp
                                                                    uu___351_11236
                                                                    =
                                                                    match uu___351_11236
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11239)
                                                                    -> true
                                                                    | 
                                                                    uu____11240
                                                                    -> false
                                                                     in
                                                                    let uu____11243
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11243
                                                                    with
                                                                    | 
                                                                    (a_ps,a_is)
                                                                    ->
                                                                    failwhen
                                                                    ((FStar_List.length
                                                                    a_ps) <>
                                                                    (FStar_List.length
                                                                    d_ps))
                                                                    "params not match?"
                                                                    (fun
                                                                    uu____11376
                                                                     ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_List.zip
                                                                    d_ps a_ps
                                                                     in
                                                                    let subst1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11438
                                                                     ->
                                                                    match uu____11438
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11458),
                                                                    (t,uu____11460))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let bs2 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst1
                                                                    bs1  in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11528
                                                                     ->
                                                                    match uu____11528
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11554),
                                                                    (t,uu____11556))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (bv, t))),
                                                                    true))
                                                                    d_ps_a_ps
                                                                     in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_List.map
                                                                    (fun
                                                                    uu____11611
                                                                     ->
                                                                    match uu____11611
                                                                    with
                                                                    | 
                                                                    (bv,aq)
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    aq))) bs2
                                                                     in
                                                                    let subpats
                                                                    =
                                                                    FStar_List.append
                                                                    subpats_1
                                                                    subpats_2
                                                                     in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    subpats))
                                                                     in
                                                                    let env =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g  in
                                                                    let equ =
                                                                    env.FStar_TypeChecker_Env.universe_of
                                                                    env s_ty
                                                                     in
                                                                    let uu____11661
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___416_11678
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___416_11678.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11661
                                                                    with
                                                                    | 
                                                                    (uu____11691,uu____11692,uu____11693,pat_t,uu____11695,uu____11696)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11702
                                                                    =
                                                                    let uu____11703
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11703
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11702
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11707
                                                                    =
                                                                    let uu____11716
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11716]
                                                                     in
                                                                    let uu____11735
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11707
                                                                    uu____11735
                                                                     in
                                                                    let nty =
                                                                    let uu____11741
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11741
                                                                     in
                                                                    let uu____11744
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11744
                                                                    (fun
                                                                    uu____11773
                                                                     ->
                                                                    match uu____11773
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false  in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____11799
                                                                    =
                                                                    let uu____11810
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11810]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11799
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11846
                                                                    =
                                                                    let uu____11857
                                                                    =
                                                                    let uu____11862
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11862)
                                                                     in
                                                                    (g', br,
                                                                    uu____11857)
                                                                     in
                                                                    ret
                                                                    uu____11846))))))
                                                                    | 
                                                                    uu____11883
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10957
                                                           (fun goal_brs  ->
                                                              let uu____11932
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11932
                                                              with
                                                              | (goals,brs,infos)
                                                                  ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                  let uu____12005
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12005
                                                                    (
                                                                    fun
                                                                    uu____12016
                                                                     ->
                                                                    let uu____12017
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12017
                                                                    (fun
                                                                    uu____12027
                                                                     ->
                                                                    ret infos))))
                                            | uu____12034 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10692
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12079::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12107 = init xs  in x :: uu____12107
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12119 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12128) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12193 = last args  in
          (match uu____12193 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12223 =
                 let uu____12224 =
                   let uu____12229 =
                     let uu____12230 =
                       let uu____12235 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12235  in
                     uu____12230 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12229, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12224  in
               FStar_All.pipe_left ret uu____12223)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12248,uu____12249) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12301 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12301 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12342 =
                      let uu____12343 =
                        let uu____12348 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12348)  in
                      FStar_Reflection_Data.Tv_Abs uu____12343  in
                    FStar_All.pipe_left ret uu____12342))
      | FStar_Syntax_Syntax.Tm_type uu____12351 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12375 ->
          let uu____12390 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12390 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12420 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12420 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12473 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12485 =
            let uu____12486 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12486  in
          FStar_All.pipe_left ret uu____12485
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12507 =
            let uu____12508 =
              let uu____12513 =
                let uu____12514 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12514  in
              (uu____12513, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12508  in
          FStar_All.pipe_left ret uu____12507
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12548 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12553 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12553 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12606 ->
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
             | FStar_Util.Inr uu____12640 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12644 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12644 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12664 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12668 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12722 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12722
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12741 =
                  let uu____12748 =
                    FStar_List.map
                      (fun uu____12760  ->
                         match uu____12760 with
                         | (p1,uu____12768) -> inspect_pat p1) ps
                     in
                  (fv, uu____12748)  in
                FStar_Reflection_Data.Pat_Cons uu____12741
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t5) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t5)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___352_12862  ->
                 match uu___352_12862 with
                 | (pat,uu____12884,t5) ->
                     let uu____12902 = inspect_pat pat  in (uu____12902, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12911 ->
          ((let uu____12913 =
              let uu____12918 =
                let uu____12919 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12920 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12919 uu____12920
                 in
              (FStar_Errors.Warning_CantInspect, uu____12918)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12913);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12119
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12933 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12933
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12937 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12937
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12941 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12941
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12948 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12948
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12973 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12973
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12990 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12990
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13009 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13009
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13013 =
          let uu____13014 =
            let uu____13021 =
              let uu____13022 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13022  in
            FStar_Syntax_Syntax.mk uu____13021  in
          uu____13014 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13013
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13030 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13030
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13039 =
          let uu____13040 =
            let uu____13047 =
              let uu____13048 =
                let uu____13061 =
                  let uu____13064 =
                    let uu____13065 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13065]  in
                  FStar_Syntax_Subst.close uu____13064 t2  in
                ((false, [lb]), uu____13061)  in
              FStar_Syntax_Syntax.Tm_let uu____13048  in
            FStar_Syntax_Syntax.mk uu____13047  in
          uu____13040 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13039
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13105 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13105 with
         | (lbs,body) ->
             let uu____13120 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13120)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13154 =
                let uu____13155 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13155  in
              FStar_All.pipe_left wrap uu____13154
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13162 =
                let uu____13163 =
                  let uu____13176 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13192 = pack_pat p1  in
                         (uu____13192, false)) ps
                     in
                  (fv, uu____13176)  in
                FStar_Syntax_Syntax.Pat_cons uu____13163  in
              FStar_All.pipe_left wrap uu____13162
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
            (fun uu___353_13238  ->
               match uu___353_13238 with
               | (pat,t1) ->
                   let uu____13255 = pack_pat pat  in
                   (uu____13255, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13303 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13303
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13331 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13331
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13377 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13377
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13416 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13416
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13433 =
        bind get
          (fun ps  ->
             let uu____13439 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13439 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13433
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13468 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___417_13475 = ps  in
                 let uu____13476 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___417_13475.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___417_13475.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___417_13475.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___417_13475.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___417_13475.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___417_13475.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___417_13475.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___417_13475.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___417_13475.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___417_13475.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___417_13475.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___417_13475.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13476
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13468
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13501 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13501 with
      | (u,ctx_uvars,g_u) ->
          let uu____13533 = FStar_List.hd ctx_uvars  in
          (match uu____13533 with
           | (ctx_uvar,uu____13547) ->
               let g =
                 let uu____13549 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13549 false
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
        let uu____13569 = goal_of_goal_ty env typ  in
        match uu____13569 with
        | (g,g_u) ->
            let ps =
              let uu____13581 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13582 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____13581;
                FStar_Tactics_Types.local_state = uu____13582
              }  in
            let uu____13589 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13589)
  