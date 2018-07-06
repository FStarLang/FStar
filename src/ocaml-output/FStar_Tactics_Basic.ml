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
      try (fun uu___356_154  -> match () with | () -> t.tac_f p) ()
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
                 let uu___357_1031 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___357_1031.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___357_1031.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___357_1031.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___357_1031.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___357_1031.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___357_1031.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___357_1031.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___357_1031.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___357_1031.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___357_1031.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___357_1031.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___357_1031.FStar_Tactics_Types.local_state)
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
           (fun uu___359_1116  ->
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
           (let uu___360_1217 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1217.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1217.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1217.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1217.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1217.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1217.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1217.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1217.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1217.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1217.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1217.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___360_1217.FStar_Tactics_Types.local_state)
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
           (fun uu___362_1247  ->
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
         let uu___363_1298 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___363_1298.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___363_1298.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___363_1298.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___364_1301 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_1301.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___364_1301.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___364_1301.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___364_1301.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_1301.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_1301.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_1301.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_1301.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_1301.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_1301.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_1301.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___364_1301.FStar_Tactics_Types.local_state)
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
         let uu___365_1347 = ps  in
         let uu____1348 =
           FStar_List.filter
             (fun g  ->
                let uu____1354 = check_goal_solved g  in
                FStar_Option.isNone uu____1354) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___365_1347.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___365_1347.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___365_1347.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1348;
           FStar_Tactics_Types.smt_goals =
             (uu___365_1347.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___365_1347.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___365_1347.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___365_1347.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___365_1347.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___365_1347.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___365_1347.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___365_1347.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___365_1347.FStar_Tactics_Types.local_state)
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
         let uu___366_1402 = p  in
         let uu____1403 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___366_1402.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___366_1402.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___366_1402.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1403;
           FStar_Tactics_Types.smt_goals =
             (uu___366_1402.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___366_1402.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___366_1402.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___366_1402.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___366_1402.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___366_1402.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___366_1402.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___366_1402.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___366_1402.FStar_Tactics_Types.local_state)
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
         (let uu___367_1493 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___367_1493.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___367_1493.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___367_1493.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___367_1493.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___367_1493.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___367_1493.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___367_1493.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___367_1493.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___367_1493.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___367_1493.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___367_1493.FStar_Tactics_Types.tac_verb_dbg);
            FStar_Tactics_Types.local_state =
              (uu___367_1493.FStar_Tactics_Types.local_state)
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
           (let uu___368_1648 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1648.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1648.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1648.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___368_1648.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_1648.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1648.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1648.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1648.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___368_1648.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___368_1648.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_1648.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___368_1648.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1668 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1668.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1668.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1668.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___369_1668.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1668.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1668.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1668.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1668.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1668.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1668.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1668.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___369_1668.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___370_1688 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1688.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1688.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1688.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1688.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1688.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1688.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1688.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1688.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1688.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1688.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1688.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1688.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___371_1708 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1708.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1708.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1708.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1708.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___371_1708.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1708.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1708.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1708.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1708.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1708.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1708.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1708.FStar_Tactics_Types.local_state)
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
           let uu___372_1941 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___372_1941.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___372_1941.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___372_1941.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___372_1941.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___372_1941.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___372_1941.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___372_1941.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___372_1941.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___372_1941.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___372_1941.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___372_1941.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___372_1941.FStar_Tactics_Types.local_state)
           }  in
         let uu____1942 = set ps1  in
         bind uu____1942
           (fun uu____1947  ->
              let uu____1948 = FStar_BigInt.of_int_fs n1  in ret uu____1948))
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1955  ->
    let uu____1958 = cur_goal ()  in
    bind uu____1958 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1990 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1990 phi  in
          let uu____1991 = new_uvar reason env typ  in
          bind uu____1991
            (fun uu____2006  ->
               match uu____2006 with
               | (uu____2013,ctx_uvar) ->
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
             (fun uu____2058  ->
                let uu____2059 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2059)
             (fun uu____2062  ->
                let e1 =
                  let uu___373_2064 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___373_2064.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___373_2064.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___373_2064.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___373_2064.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___373_2064.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___373_2064.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___373_2064.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___373_2064.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___373_2064.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___373_2064.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___373_2064.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___373_2064.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___373_2064.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___373_2064.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___373_2064.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___373_2064.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___373_2064.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___373_2064.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___373_2064.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___373_2064.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___373_2064.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___373_2064.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___373_2064.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___373_2064.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___373_2064.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___373_2064.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___373_2064.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___373_2064.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___373_2064.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___373_2064.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___373_2064.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___373_2064.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___373_2064.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___373_2064.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___373_2064.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___373_2064.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___373_2064.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___373_2064.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___373_2064.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___373_2064.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___373_2064.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___375_2075  ->
                     match () with
                     | () ->
                         let uu____2084 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2084) ()
                with
                | FStar_Errors.Err (uu____2111,msg) ->
                    let uu____2113 = tts e1 t  in
                    let uu____2114 =
                      let uu____2115 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2115
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2113 uu____2114 msg
                | FStar_Errors.Error (uu____2122,msg,uu____2124) ->
                    let uu____2125 = tts e1 t  in
                    let uu____2126 =
                      let uu____2127 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2127
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2125 uu____2126 msg))
  
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
  fun uu____2154  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___376_2172 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___376_2172.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___376_2172.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___376_2172.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___376_2172.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___376_2172.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___376_2172.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___376_2172.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___376_2172.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___376_2172.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___376_2172.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___376_2172.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___376_2172.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2196 = get_guard_policy ()  in
      bind uu____2196
        (fun old_pol  ->
           let uu____2202 = set_guard_policy pol  in
           bind uu____2202
             (fun uu____2206  ->
                bind t
                  (fun r  ->
                     let uu____2210 = set_guard_policy old_pol  in
                     bind uu____2210 (fun uu____2214  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2217 = let uu____2222 = cur_goal ()  in trytac uu____2222  in
  bind uu____2217
    (fun uu___347_2229  ->
       match uu___347_2229 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2235 = FStar_Options.peek ()  in ret uu____2235)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2257  ->
             let uu____2258 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2258)
          (fun uu____2261  ->
             let uu____2262 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2262
               (fun uu____2266  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2270 =
                         let uu____2271 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2271.FStar_TypeChecker_Env.guard_f  in
                       match uu____2270 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2275 = istrivial e f  in
                           if uu____2275
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2285 =
                                          let uu____2290 =
                                            let uu____2291 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2291
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2290)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2285);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2294  ->
                                           let uu____2295 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2295)
                                        (fun uu____2298  ->
                                           let uu____2299 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2299
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___377_2306 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___377_2306.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___377_2306.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___377_2306.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2309  ->
                                           let uu____2310 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2310)
                                        (fun uu____2313  ->
                                           let uu____2314 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2314
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___378_2321 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___378_2321.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___378_2321.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___378_2321.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2324  ->
                                           let uu____2325 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2325)
                                        (fun uu____2327  ->
                                           try
                                             (fun uu___380_2332  ->
                                                match () with
                                                | () ->
                                                    let uu____2335 =
                                                      let uu____2336 =
                                                        let uu____2337 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2337
                                                         in
                                                      Prims.op_Negation
                                                        uu____2336
                                                       in
                                                    if uu____2335
                                                    then
                                                      mlog
                                                        (fun uu____2342  ->
                                                           let uu____2343 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2343)
                                                        (fun uu____2345  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___379_2348 ->
                                               mlog
                                                 (fun uu____2353  ->
                                                    let uu____2354 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2354)
                                                 (fun uu____2356  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2366 =
      let uu____2369 = cur_goal ()  in
      bind uu____2369
        (fun goal  ->
           let uu____2375 =
             let uu____2384 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2384 t  in
           bind uu____2375
             (fun uu____2395  ->
                match uu____2395 with
                | (uu____2404,typ,uu____2406) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2366
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2435 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2435 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2446  ->
    let uu____2449 = cur_goal ()  in
    bind uu____2449
      (fun goal  ->
         let uu____2455 =
           let uu____2456 = FStar_Tactics_Types.goal_env goal  in
           let uu____2457 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2456 uu____2457  in
         if uu____2455
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2461 =
              let uu____2462 = FStar_Tactics_Types.goal_env goal  in
              let uu____2463 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2462 uu____2463  in
            fail1 "Not a trivial goal: %s" uu____2461))
  
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
          let uu____2492 =
            let uu____2493 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2493.FStar_TypeChecker_Env.guard_f  in
          match uu____2492 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2501 = istrivial e f  in
              if uu____2501
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2509 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2509
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___381_2519 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___381_2519.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___381_2519.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___381_2519.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2526  ->
    let uu____2529 = cur_goal ()  in
    bind uu____2529
      (fun g  ->
         let uu____2535 = is_irrelevant g  in
         if uu____2535
         then bind __dismiss (fun uu____2539  -> add_smt_goals [g])
         else
           (let uu____2541 =
              let uu____2542 = FStar_Tactics_Types.goal_env g  in
              let uu____2543 = FStar_Tactics_Types.goal_type g  in
              tts uu____2542 uu____2543  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2541))
  
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
             let uu____2592 =
               try
                 (fun uu___386_2615  ->
                    match () with
                    | () ->
                        let uu____2626 =
                          let uu____2635 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2635
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2626) ()
               with | uu___385_2645 -> fail "divide: not enough goals"  in
             bind uu____2592
               (fun uu____2681  ->
                  match uu____2681 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___382_2707 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___382_2707.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___382_2707.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___382_2707.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___382_2707.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___382_2707.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___382_2707.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___382_2707.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___382_2707.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___382_2707.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___382_2707.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___382_2707.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2708 = set lp  in
                      bind uu____2708
                        (fun uu____2716  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___383_2732 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___383_2732.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___383_2732.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___383_2732.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___383_2732.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___383_2732.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___383_2732.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___383_2732.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___383_2732.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___383_2732.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___383_2732.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___383_2732.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2733 = set rp  in
                                     bind uu____2733
                                       (fun uu____2741  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___384_2757 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___384_2757.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___384_2757.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2758 = set p'
                                                       in
                                                    bind uu____2758
                                                      (fun uu____2766  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2772 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2793 = divide FStar_BigInt.one f idtac  in
    bind uu____2793
      (fun uu____2806  -> match uu____2806 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2843::uu____2844 ->
             let uu____2847 =
               let uu____2856 = map tau  in
               divide FStar_BigInt.one tau uu____2856  in
             bind uu____2847
               (fun uu____2874  ->
                  match uu____2874 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2915 =
        bind t1
          (fun uu____2920  ->
             let uu____2921 = map t2  in
             bind uu____2921 (fun uu____2929  -> ret ()))
         in
      focus uu____2915
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2938  ->
    let uu____2941 =
      let uu____2944 = cur_goal ()  in
      bind uu____2944
        (fun goal  ->
           let uu____2953 =
             let uu____2960 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2960  in
           match uu____2953 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2969 =
                 let uu____2970 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2970  in
               if uu____2969
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2975 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2975 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2989 = new_uvar "intro" env' typ'  in
                  bind uu____2989
                    (fun uu____3005  ->
                       match uu____3005 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3029 = set_solution goal sol  in
                           bind uu____3029
                             (fun uu____3035  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3037 =
                                  let uu____3040 = bnorm_goal g  in
                                  replace_cur uu____3040  in
                                bind uu____3037 (fun uu____3042  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3047 =
                 let uu____3048 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3049 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3048 uu____3049  in
               fail1 "goal is not an arrow (%s)" uu____3047)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2941
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3064  ->
    let uu____3071 = cur_goal ()  in
    bind uu____3071
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3088 =
            let uu____3095 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3095  in
          match uu____3088 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3108 =
                let uu____3109 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3109  in
              if uu____3108
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3122 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3122
                    in
                 let bs =
                   let uu____3132 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3132; b]  in
                 let env' =
                   let uu____3158 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3158 bs  in
                 let uu____3159 =
                   let uu____3166 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3166  in
                 bind uu____3159
                   (fun uu____3185  ->
                      match uu____3185 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3199 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3202 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3199
                              FStar_Parser_Const.effect_Tot_lid uu____3202 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3220 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3220 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3242 =
                                   let uu____3243 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3243.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3242
                                  in
                               let uu____3256 = set_solution goal tm  in
                               bind uu____3256
                                 (fun uu____3265  ->
                                    let uu____3266 =
                                      let uu____3269 =
                                        bnorm_goal
                                          (let uu___387_3272 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___387_3272.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___387_3272.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___387_3272.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3269  in
                                    bind uu____3266
                                      (fun uu____3279  ->
                                         let uu____3280 =
                                           let uu____3285 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3285, b)  in
                                         ret uu____3280)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3294 =
                let uu____3295 = FStar_Tactics_Types.goal_env goal  in
                let uu____3296 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3295 uu____3296  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3294))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3314 = cur_goal ()  in
    bind uu____3314
      (fun goal  ->
         mlog
           (fun uu____3321  ->
              let uu____3322 =
                let uu____3323 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3323  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3322)
           (fun uu____3328  ->
              let steps =
                let uu____3332 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3332
                 in
              let t =
                let uu____3336 = FStar_Tactics_Types.goal_env goal  in
                let uu____3337 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3336 uu____3337  in
              let uu____3338 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3338))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3362 =
          mlog
            (fun uu____3367  ->
               let uu____3368 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3368)
            (fun uu____3370  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3376 -> g.FStar_Tactics_Types.opts
                      | uu____3379 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3384  ->
                         let uu____3385 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3385)
                      (fun uu____3388  ->
                         let uu____3389 = __tc e t  in
                         bind uu____3389
                           (fun uu____3410  ->
                              match uu____3410 with
                              | (t1,uu____3420,uu____3421) ->
                                  let steps =
                                    let uu____3425 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3425
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3362
  
let (refine_intro : unit -> unit tac) =
  fun uu____3439  ->
    let uu____3442 =
      let uu____3445 = cur_goal ()  in
      bind uu____3445
        (fun g  ->
           let uu____3452 =
             let uu____3463 = FStar_Tactics_Types.goal_env g  in
             let uu____3464 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3463 uu____3464
              in
           match uu____3452 with
           | (uu____3467,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3492 =
                 let uu____3497 =
                   let uu____3502 =
                     let uu____3503 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3503]  in
                   FStar_Syntax_Subst.open_term uu____3502 phi  in
                 match uu____3497 with
                 | (bvs,phi1) ->
                     let uu____3528 =
                       let uu____3529 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3529  in
                     (uu____3528, phi1)
                  in
               (match uu____3492 with
                | (bv1,phi1) ->
                    let uu____3548 =
                      let uu____3551 = FStar_Tactics_Types.goal_env g  in
                      let uu____3552 =
                        let uu____3553 =
                          let uu____3556 =
                            let uu____3557 =
                              let uu____3564 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3564)  in
                            FStar_Syntax_Syntax.NT uu____3557  in
                          [uu____3556]  in
                        FStar_Syntax_Subst.subst uu____3553 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3551
                        uu____3552 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3548
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3572  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3442
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3591 = cur_goal ()  in
      bind uu____3591
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3599 = FStar_Tactics_Types.goal_env goal  in
               let uu____3600 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3599 uu____3600
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3602 = __tc env t  in
           bind uu____3602
             (fun uu____3621  ->
                match uu____3621 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3636  ->
                         let uu____3637 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3638 =
                           let uu____3639 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3639
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3637 uu____3638)
                      (fun uu____3642  ->
                         let uu____3643 =
                           let uu____3646 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3646 guard  in
                         bind uu____3643
                           (fun uu____3648  ->
                              mlog
                                (fun uu____3652  ->
                                   let uu____3653 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3654 =
                                     let uu____3655 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3655
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3653 uu____3654)
                                (fun uu____3658  ->
                                   let uu____3659 =
                                     let uu____3662 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3663 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3662 typ uu____3663  in
                                   bind uu____3659
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3669 =
                                             let uu____3670 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3670 t1  in
                                           let uu____3671 =
                                             let uu____3672 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3672 typ  in
                                           let uu____3673 =
                                             let uu____3674 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3675 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3674 uu____3675  in
                                           let uu____3676 =
                                             let uu____3677 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3678 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3677 uu____3678  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3669 uu____3671 uu____3673
                                             uu____3676)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3698 =
          mlog
            (fun uu____3703  ->
               let uu____3704 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3704)
            (fun uu____3707  ->
               let uu____3708 =
                 let uu____3715 = __exact_now set_expected_typ1 tm  in
                 catch uu____3715  in
               bind uu____3708
                 (fun uu___349_3724  ->
                    match uu___349_3724 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3735  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3738  ->
                             let uu____3739 =
                               let uu____3746 =
                                 let uu____3749 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3749
                                   (fun uu____3754  ->
                                      let uu____3755 = refine_intro ()  in
                                      bind uu____3755
                                        (fun uu____3759  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3746  in
                             bind uu____3739
                               (fun uu___348_3766  ->
                                  match uu___348_3766 with
                                  | FStar_Util.Inr r -> ret ()
                                  | FStar_Util.Inl uu____3774 -> fail e))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3698
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3824 = f x  in
          bind uu____3824
            (fun y  ->
               let uu____3832 = mapM f xs  in
               bind uu____3832 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3903 = do_unify e ty1 ty2  in
          bind uu____3903
            (fun uu___350_3915  ->
               if uu___350_3915
               then ret acc
               else
                 (let uu____3934 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3934 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3955 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3956 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3955
                        uu____3956
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3971 =
                        let uu____3972 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3972  in
                      if uu____3971
                      then fail "Codomain is effectful"
                      else
                        (let uu____3992 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3992
                           (fun uu____4018  ->
                              match uu____4018 with
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
      let uu____4104 =
        mlog
          (fun uu____4109  ->
             let uu____4110 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4110)
          (fun uu____4113  ->
             let uu____4114 = cur_goal ()  in
             bind uu____4114
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4122 = __tc e tm  in
                  bind uu____4122
                    (fun uu____4143  ->
                       match uu____4143 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4156 =
                             let uu____4167 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4167  in
                           bind uu____4156
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4210  ->
                                       fun w  ->
                                         match uu____4210 with
                                         | (uvt,q,uu____4228) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4260 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4277  ->
                                       fun s  ->
                                         match uu____4277 with
                                         | (uu____4289,uu____4290,uv) ->
                                             let uu____4292 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4292) uvs uu____4260
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4301 = solve' goal w  in
                                bind uu____4301
                                  (fun uu____4306  ->
                                     let uu____4307 =
                                       mapM
                                         (fun uu____4324  ->
                                            match uu____4324 with
                                            | (uvt,q,uv) ->
                                                let uu____4336 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4336 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4341 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4342 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4342
                                                     then ret ()
                                                     else
                                                       (let uu____4346 =
                                                          let uu____4349 =
                                                            bnorm_goal
                                                              (let uu___388_4352
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___388_4352.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___388_4352.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4349]  in
                                                        add_goals uu____4346)))
                                         uvs
                                        in
                                     bind uu____4307
                                       (fun uu____4356  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4104
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4381 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4381
    then
      let uu____4388 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4403 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4456 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4388 with
      | (pre,post) ->
          let post1 =
            let uu____4488 =
              let uu____4499 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4499]  in
            FStar_Syntax_Util.mk_app post uu____4488  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4529 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4529
       then
         let uu____4536 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4536
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4569 =
      let uu____4572 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4579  ->
                  let uu____4580 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4580)
               (fun uu____4584  ->
                  let is_unit_t t =
                    let uu____4591 =
                      let uu____4592 = FStar_Syntax_Subst.compress t  in
                      uu____4592.FStar_Syntax_Syntax.n  in
                    match uu____4591 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4596 -> false  in
                  let uu____4597 = cur_goal ()  in
                  bind uu____4597
                    (fun goal  ->
                       let uu____4603 =
                         let uu____4612 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4612 tm  in
                       bind uu____4603
                         (fun uu____4627  ->
                            match uu____4627 with
                            | (tm1,t,guard) ->
                                let uu____4639 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4639 with
                                 | (bs,comp) ->
                                     let uu____4672 = lemma_or_sq comp  in
                                     (match uu____4672 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4691 =
                                            FStar_List.fold_left
                                              (fun uu____4739  ->
                                                 fun uu____4740  ->
                                                   match (uu____4739,
                                                           uu____4740)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4853 =
                                                         is_unit_t b_t  in
                                                       if uu____4853
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4891 =
                                                            let uu____4904 =
                                                              let uu____4905
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____4905.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____4908 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____4904
                                                              uu____4908 b_t
                                                             in
                                                          match uu____4891
                                                          with
                                                          | (u,uu____4926,g_u)
                                                              ->
                                                              let uu____4940
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4940,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4691 with
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
                                               let uu____5019 =
                                                 let uu____5022 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5023 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5024 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5022
                                                   uu____5023 uu____5024
                                                  in
                                               bind uu____5019
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5032 =
                                                        let uu____5033 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5033 tm1
                                                         in
                                                      let uu____5034 =
                                                        let uu____5035 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5036 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5035
                                                          uu____5036
                                                         in
                                                      let uu____5037 =
                                                        let uu____5038 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5039 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5038
                                                          uu____5039
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5032 uu____5034
                                                        uu____5037
                                                    else
                                                      (let uu____5041 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5041
                                                         (fun uu____5046  ->
                                                            let uu____5047 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5047
                                                              (fun uu____5055
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5080
                                                                    =
                                                                    let uu____5083
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5083
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5080
                                                                     in
                                                                   FStar_List.existsML
                                                                    (fun u 
                                                                    ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                    in
                                                                 let appears
                                                                   uv goals1
                                                                   =
                                                                   FStar_List.existsML
                                                                    (fun g' 
                                                                    ->
                                                                    let uu____5118
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5118)
                                                                    goals1
                                                                    in
                                                                 let checkone
                                                                   t1 goals1
                                                                   =
                                                                   let uu____5134
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5134
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5152)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5178)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals1
                                                                    | 
                                                                    uu____5195
                                                                    -> false)
                                                                    in
                                                                 let uu____5196
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
                                                                    let uu____5226
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5226
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5248)
                                                                    ->
                                                                    let uu____5273
                                                                    =
                                                                    let uu____5274
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5274.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5273
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5282)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___389_5302
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___389_5302.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___389_5302.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___389_5302.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5305
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5311
                                                                     ->
                                                                    let uu____5312
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5313
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5312
                                                                    uu____5313)
                                                                    (fun
                                                                    uu____5318
                                                                     ->
                                                                    let env =
                                                                    let uu___390_5320
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___390_5320.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5322
                                                                    =
                                                                    let uu____5325
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5326
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5327
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5326
                                                                    uu____5327
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5329
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5325
                                                                    uu____5329
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5322
                                                                    (fun
                                                                    uu____5333
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5196
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
                                                                    let uu____5395
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5395
                                                                    then
                                                                    let uu____5398
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5398
                                                                    else
                                                                    filter' f
                                                                    xs1  in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun
                                                                    goals1 
                                                                    ->
                                                                    let uu____5412
                                                                    =
                                                                    let uu____5413
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5413
                                                                    goals1
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5412)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5414
                                                                    =
                                                                    let uu____5417
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5417
                                                                    guard  in
                                                                    bind
                                                                    uu____5414
                                                                    (fun
                                                                    uu____5420
                                                                     ->
                                                                    let uu____5421
                                                                    =
                                                                    let uu____5424
                                                                    =
                                                                    let uu____5425
                                                                    =
                                                                    let uu____5426
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5427
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5426
                                                                    uu____5427
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5425
                                                                     in
                                                                    if
                                                                    uu____5424
                                                                    then
                                                                    let uu____5430
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5430
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5421
                                                                    (fun
                                                                    uu____5433
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4572  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4569
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5455 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5455 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5465::(e1,uu____5467)::(e2,uu____5469)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5530 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5554 = destruct_eq' typ  in
    match uu____5554 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5584 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5584 with
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
        let uu____5646 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5646 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5694 = aux e'  in
               FStar_Util.map_opt uu____5694
                 (fun uu____5718  ->
                    match uu____5718 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5739 = aux e  in
      FStar_Util.map_opt uu____5739
        (fun uu____5763  ->
           match uu____5763 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5830 =
            let uu____5839 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5839  in
          FStar_Util.map_opt uu____5830
            (fun uu____5854  ->
               match uu____5854 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___391_5873 = bv  in
                     let uu____5874 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___391_5873.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___391_5873.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5874
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___392_5882 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5883 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5892 =
                       let uu____5895 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5895  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___392_5882.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5883;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5892;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___392_5882.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___392_5882.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___392_5882.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___393_5896 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___393_5896.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___393_5896.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___393_5896.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5906 =
      let uu____5909 = cur_goal ()  in
      bind uu____5909
        (fun goal  ->
           let uu____5917 = h  in
           match uu____5917 with
           | (bv,uu____5921) ->
               mlog
                 (fun uu____5929  ->
                    let uu____5930 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5931 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5930
                      uu____5931)
                 (fun uu____5934  ->
                    let uu____5935 =
                      let uu____5944 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5944  in
                    match uu____5935 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5965 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5965 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5980 =
                               let uu____5981 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5981.FStar_Syntax_Syntax.n  in
                             (match uu____5980 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___394_5998 = bv1  in
                                    let uu____5999 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___394_5998.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___394_5998.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5999
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___395_6007 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6008 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6017 =
                                      let uu____6020 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6020
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___395_6007.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6008;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6017;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___395_6007.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___395_6007.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___395_6007.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___396_6023 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___396_6023.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___396_6023.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___396_6023.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6024 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6025 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5906
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6050 =
        let uu____6053 = cur_goal ()  in
        bind uu____6053
          (fun goal  ->
             let uu____6064 = b  in
             match uu____6064 with
             | (bv,uu____6068) ->
                 let bv' =
                   let uu____6074 =
                     let uu___397_6075 = bv  in
                     let uu____6076 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6076;
                       FStar_Syntax_Syntax.index =
                         (uu___397_6075.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___397_6075.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6074  in
                 let s1 =
                   let uu____6080 =
                     let uu____6081 =
                       let uu____6088 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6088)  in
                     FStar_Syntax_Syntax.NT uu____6081  in
                   [uu____6080]  in
                 let uu____6093 = subst_goal bv bv' s1 goal  in
                 (match uu____6093 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6050
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6112 =
      let uu____6115 = cur_goal ()  in
      bind uu____6115
        (fun goal  ->
           let uu____6124 = b  in
           match uu____6124 with
           | (bv,uu____6128) ->
               let uu____6133 =
                 let uu____6142 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6142  in
               (match uu____6133 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6163 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6163 with
                     | (ty,u) ->
                         let uu____6172 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6172
                           (fun uu____6190  ->
                              match uu____6190 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___398_6200 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___398_6200.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___398_6200.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6204 =
                                      let uu____6205 =
                                        let uu____6212 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6212)  in
                                      FStar_Syntax_Syntax.NT uu____6205  in
                                    [uu____6204]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___399_6224 = b1  in
                                         let uu____6225 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___399_6224.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___399_6224.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6225
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6232  ->
                                       let new_goal =
                                         let uu____6234 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6235 =
                                           let uu____6236 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6236
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6234 uu____6235
                                          in
                                       let uu____6237 = add_goals [new_goal]
                                          in
                                       bind uu____6237
                                         (fun uu____6242  ->
                                            let uu____6243 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6243
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6112
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6266 =
        let uu____6269 = cur_goal ()  in
        bind uu____6269
          (fun goal  ->
             let uu____6278 = b  in
             match uu____6278 with
             | (bv,uu____6282) ->
                 let uu____6287 =
                   let uu____6296 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6296  in
                 (match uu____6287 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6320 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6320
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___400_6325 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___400_6325.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___400_6325.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6327 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6327))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6266
  
let (revert : unit -> unit tac) =
  fun uu____6338  ->
    let uu____6341 = cur_goal ()  in
    bind uu____6341
      (fun goal  ->
         let uu____6347 =
           let uu____6354 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6354  in
         match uu____6347 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6370 =
                 let uu____6373 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6373  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6370
                in
             let uu____6388 = new_uvar "revert" env' typ'  in
             bind uu____6388
               (fun uu____6403  ->
                  match uu____6403 with
                  | (r,u_r) ->
                      let uu____6412 =
                        let uu____6415 =
                          let uu____6416 =
                            let uu____6417 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6417.FStar_Syntax_Syntax.pos  in
                          let uu____6420 =
                            let uu____6425 =
                              let uu____6426 =
                                let uu____6435 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6435  in
                              [uu____6426]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6425  in
                          uu____6420 FStar_Pervasives_Native.None uu____6416
                           in
                        set_solution goal uu____6415  in
                      bind uu____6412
                        (fun uu____6456  ->
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
      let uu____6468 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6468
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6483 = cur_goal ()  in
    bind uu____6483
      (fun goal  ->
         mlog
           (fun uu____6491  ->
              let uu____6492 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6493 =
                let uu____6494 =
                  let uu____6495 =
                    let uu____6504 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6504  in
                  FStar_All.pipe_right uu____6495 FStar_List.length  in
                FStar_All.pipe_right uu____6494 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6492 uu____6493)
           (fun uu____6521  ->
              let uu____6522 =
                let uu____6531 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6531  in
              match uu____6522 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6570 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6570
                        then
                          let uu____6573 =
                            let uu____6574 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6574
                             in
                          fail uu____6573
                        else check1 bvs2
                     in
                  let uu____6576 =
                    let uu____6577 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6577  in
                  if uu____6576
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6581 = check1 bvs  in
                     bind uu____6581
                       (fun uu____6587  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6589 =
                            let uu____6596 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6596  in
                          bind uu____6589
                            (fun uu____6605  ->
                               match uu____6605 with
                               | (ut,uvar_ut) ->
                                   let uu____6614 = set_solution goal ut  in
                                   bind uu____6614
                                     (fun uu____6619  ->
                                        let uu____6620 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6620))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6627  ->
    let uu____6630 = cur_goal ()  in
    bind uu____6630
      (fun goal  ->
         let uu____6636 =
           let uu____6643 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6643  in
         match uu____6636 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6651) ->
             let uu____6656 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6656)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6666 = cur_goal ()  in
    bind uu____6666
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6676 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6676  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6679  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6689 = cur_goal ()  in
    bind uu____6689
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6699 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6699  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6702  -> add_goals [g']))
  
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
            let uu____6742 = FStar_Syntax_Subst.compress t  in
            uu____6742.FStar_Syntax_Syntax.n  in
          let uu____6745 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___404_6751 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___404_6751.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___404_6751.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6745
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6767 =
                   let uu____6768 = FStar_Syntax_Subst.compress t1  in
                   uu____6768.FStar_Syntax_Syntax.n  in
                 match uu____6767 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6799 = ff hd1  in
                     bind uu____6799
                       (fun hd2  ->
                          let fa uu____6825 =
                            match uu____6825 with
                            | (a,q) ->
                                let uu____6846 = ff a  in
                                bind uu____6846 (fun a1  -> ret (a1, q))
                             in
                          let uu____6865 = mapM fa args  in
                          bind uu____6865
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6947 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6947 with
                      | (bs1,t') ->
                          let uu____6956 =
                            let uu____6959 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6959 t'  in
                          bind uu____6956
                            (fun t''  ->
                               let uu____6963 =
                                 let uu____6964 =
                                   let uu____6983 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6992 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6983, uu____6992, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6964  in
                               ret uu____6963))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7067 = ff hd1  in
                     bind uu____7067
                       (fun hd2  ->
                          let ffb br =
                            let uu____7082 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7082 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7114 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7114  in
                                let uu____7115 = ff1 e  in
                                bind uu____7115
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7130 = mapM ffb brs  in
                          bind uu____7130
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7174;
                          FStar_Syntax_Syntax.lbtyp = uu____7175;
                          FStar_Syntax_Syntax.lbeff = uu____7176;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7178;
                          FStar_Syntax_Syntax.lbpos = uu____7179;_}::[]),e)
                     ->
                     let lb =
                       let uu____7204 =
                         let uu____7205 = FStar_Syntax_Subst.compress t1  in
                         uu____7205.FStar_Syntax_Syntax.n  in
                       match uu____7204 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7209) -> lb
                       | uu____7222 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7231 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7231
                         (fun def1  ->
                            ret
                              (let uu___401_7237 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___401_7237.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___401_7237.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___401_7237.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___401_7237.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___401_7237.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___401_7237.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7238 = fflb lb  in
                     bind uu____7238
                       (fun lb1  ->
                          let uu____7248 =
                            let uu____7253 =
                              let uu____7254 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7254]  in
                            FStar_Syntax_Subst.open_term uu____7253 e  in
                          match uu____7248 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7284 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7284  in
                              let uu____7285 = ff1 e1  in
                              bind uu____7285
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7326 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7326
                         (fun def  ->
                            ret
                              (let uu___402_7332 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___402_7332.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___402_7332.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___402_7332.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___402_7332.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___402_7332.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___402_7332.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7333 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7333 with
                      | (lbs1,e1) ->
                          let uu____7348 = mapM fflb lbs1  in
                          bind uu____7348
                            (fun lbs2  ->
                               let uu____7360 = ff e1  in
                               bind uu____7360
                                 (fun e2  ->
                                    let uu____7368 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7368 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7436 = ff t2  in
                     bind uu____7436
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7467 = ff t2  in
                     bind uu____7467
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7474 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___403_7481 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___403_7481.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___403_7481.FStar_Syntax_Syntax.vars)
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
            let uu____7518 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___405_7527 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___405_7527.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___405_7527.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___405_7527.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___405_7527.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___405_7527.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___405_7527.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___405_7527.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___405_7527.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___405_7527.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___405_7527.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___405_7527.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___405_7527.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___405_7527.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___405_7527.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___405_7527.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___405_7527.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___405_7527.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___405_7527.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___405_7527.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___405_7527.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___405_7527.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___405_7527.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___405_7527.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___405_7527.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___405_7527.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___405_7527.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___405_7527.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___405_7527.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___405_7527.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___405_7527.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___405_7527.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___405_7527.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___405_7527.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___405_7527.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___405_7527.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___405_7527.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___405_7527.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___405_7527.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___405_7527.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___405_7527.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___405_7527.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7518 with
            | (t1,lcomp,g) ->
                let uu____7533 =
                  (let uu____7536 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7536) ||
                    (let uu____7538 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7538)
                   in
                if uu____7533
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7546 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7546
                       (fun uu____7562  ->
                          match uu____7562 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7575  ->
                                    let uu____7576 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7577 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7576 uu____7577);
                               (let uu____7578 =
                                  let uu____7581 =
                                    let uu____7582 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7582 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7581
                                    opts
                                   in
                                bind uu____7578
                                  (fun uu____7585  ->
                                     let uu____7586 =
                                       bind tau
                                         (fun uu____7592  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7598  ->
                                                 let uu____7599 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7600 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7599 uu____7600);
                                            ret ut1)
                                        in
                                     focus uu____7586))))
                      in
                   let uu____7601 = catch rewrite_eq  in
                   bind uu____7601
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
          let uu____7799 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7799
            (fun t1  ->
               let uu____7807 =
                 f env
                   (let uu___408_7816 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___408_7816.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___408_7816.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7807
                 (fun uu____7832  ->
                    match uu____7832 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7855 =
                               let uu____7856 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7856.FStar_Syntax_Syntax.n  in
                             match uu____7855 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7893 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7893
                                   (fun uu____7918  ->
                                      match uu____7918 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7934 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7934
                                            (fun uu____7961  ->
                                               match uu____7961 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___406_7991 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___406_7991.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___406_7991.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8033 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8033 with
                                  | (bs1,t') ->
                                      let uu____8048 =
                                        let uu____8055 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8055 ctrl1 t'
                                         in
                                      bind uu____8048
                                        (fun uu____8073  ->
                                           match uu____8073 with
                                           | (t'',ctrl2) ->
                                               let uu____8088 =
                                                 let uu____8095 =
                                                   let uu___407_8098 = t4  in
                                                   let uu____8101 =
                                                     let uu____8102 =
                                                       let uu____8121 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8130 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8121,
                                                         uu____8130, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8102
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8101;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___407_8098.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___407_8098.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8095, ctrl2)  in
                                               ret uu____8088))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8183 -> ret (t3, ctrl1))))

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
              let uu____8230 = ctrl_tac_fold f env ctrl t  in
              bind uu____8230
                (fun uu____8254  ->
                   match uu____8254 with
                   | (t1,ctrl1) ->
                       let uu____8269 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8269
                         (fun uu____8296  ->
                            match uu____8296 with
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
              let uu____8380 =
                let uu____8387 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8387
                  (fun uu____8396  ->
                     let uu____8397 = ctrl t1  in
                     bind uu____8397
                       (fun res  ->
                          let uu____8420 = trivial ()  in
                          bind uu____8420 (fun uu____8428  -> ret res)))
                 in
              bind uu____8380
                (fun uu____8444  ->
                   match uu____8444 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8468 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___409_8477 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___409_8477.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___409_8477.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___409_8477.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___409_8477.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___409_8477.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___409_8477.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___409_8477.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___409_8477.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___409_8477.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___409_8477.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___409_8477.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___409_8477.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___409_8477.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___409_8477.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___409_8477.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___409_8477.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___409_8477.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___409_8477.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___409_8477.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___409_8477.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___409_8477.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___409_8477.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___409_8477.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___409_8477.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___409_8477.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___409_8477.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___409_8477.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___409_8477.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___409_8477.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___409_8477.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___409_8477.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___409_8477.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___409_8477.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___409_8477.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___409_8477.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___409_8477.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___409_8477.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___409_8477.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___409_8477.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___409_8477.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___409_8477.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8468 with
                          | (t2,lcomp,g) ->
                              let uu____8487 =
                                (let uu____8490 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8490) ||
                                  (let uu____8492 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8492)
                                 in
                              if uu____8487
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8505 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8505
                                   (fun uu____8525  ->
                                      match uu____8525 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8542  ->
                                                let uu____8543 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8544 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8543 uu____8544);
                                           (let uu____8545 =
                                              let uu____8548 =
                                                let uu____8549 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8549 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8548 opts
                                               in
                                            bind uu____8545
                                              (fun uu____8556  ->
                                                 let uu____8557 =
                                                   bind rewriter
                                                     (fun uu____8571  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8577  ->
                                                             let uu____8578 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8579 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8578
                                                               uu____8579);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8557)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8620 =
        bind get
          (fun ps  ->
             let uu____8630 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8630 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8667  ->
                       let uu____8668 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8668);
                  bind dismiss_all
                    (fun uu____8671  ->
                       let uu____8672 =
                         let uu____8679 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8679
                           keepGoing gt1
                          in
                       bind uu____8672
                         (fun uu____8691  ->
                            match uu____8691 with
                            | (gt',uu____8699) ->
                                (log ps
                                   (fun uu____8703  ->
                                      let uu____8704 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8704);
                                 (let uu____8705 = push_goals gs  in
                                  bind uu____8705
                                    (fun uu____8710  ->
                                       let uu____8711 =
                                         let uu____8714 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8714]  in
                                       add_goals uu____8711)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8620
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8737 =
        bind get
          (fun ps  ->
             let uu____8747 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8747 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8784  ->
                       let uu____8785 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8785);
                  bind dismiss_all
                    (fun uu____8788  ->
                       let uu____8789 =
                         let uu____8792 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8792 gt1
                          in
                       bind uu____8789
                         (fun gt'  ->
                            log ps
                              (fun uu____8800  ->
                                 let uu____8801 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8801);
                            (let uu____8802 = push_goals gs  in
                             bind uu____8802
                               (fun uu____8807  ->
                                  let uu____8808 =
                                    let uu____8811 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8811]  in
                                  add_goals uu____8808))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8737
  
let (trefl : unit -> unit tac) =
  fun uu____8822  ->
    let uu____8825 =
      let uu____8828 = cur_goal ()  in
      bind uu____8828
        (fun g  ->
           let uu____8846 =
             let uu____8851 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8851  in
           match uu____8846 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8859 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8859 with
                | (hd1,args) ->
                    let uu____8898 =
                      let uu____8911 =
                        let uu____8912 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8912.FStar_Syntax_Syntax.n  in
                      (uu____8911, args)  in
                    (match uu____8898 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8926::(l,uu____8928)::(r,uu____8930)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8977 =
                           let uu____8980 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8980 l r  in
                         bind uu____8977
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8987 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8987 l
                                    in
                                 let r1 =
                                   let uu____8989 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8989 r
                                    in
                                 let uu____8990 =
                                   let uu____8993 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8993 l1 r1  in
                                 bind uu____8990
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8999 =
                                           let uu____9000 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9000 l1  in
                                         let uu____9001 =
                                           let uu____9002 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9002 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8999 uu____9001))))
                     | (hd2,uu____9004) ->
                         let uu____9021 =
                           let uu____9022 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9022 t  in
                         fail1 "trefl: not an equality (%s)" uu____9021))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8825
  
let (dup : unit -> unit tac) =
  fun uu____9035  ->
    let uu____9038 = cur_goal ()  in
    bind uu____9038
      (fun g  ->
         let uu____9044 =
           let uu____9051 = FStar_Tactics_Types.goal_env g  in
           let uu____9052 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9051 uu____9052  in
         bind uu____9044
           (fun uu____9061  ->
              match uu____9061 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___410_9071 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___410_9071.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___410_9071.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___410_9071.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9074  ->
                       let uu____9075 =
                         let uu____9078 = FStar_Tactics_Types.goal_env g  in
                         let uu____9079 =
                           let uu____9080 =
                             let uu____9081 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9082 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9081
                               uu____9082
                              in
                           let uu____9083 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9084 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9080 uu____9083 u
                             uu____9084
                            in
                         add_irrelevant_goal "dup equation" uu____9078
                           uu____9079 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9075
                         (fun uu____9087  ->
                            let uu____9088 = add_goals [g']  in
                            bind uu____9088 (fun uu____9092  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9099  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___411_9116 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___411_9116.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___411_9116.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___411_9116.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___411_9116.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___411_9116.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___411_9116.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___411_9116.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___411_9116.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___411_9116.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___411_9116.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___411_9116.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___411_9116.FStar_Tactics_Types.local_state)
                })
         | uu____9117 -> fail "flip: less than 2 goals")
  
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
              let uu____9242 = f x y  in
              if uu____9242 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9262 -> (acc, l11, l21)  in
        let uu____9277 = aux [] l1 l2  in
        match uu____9277 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9382 = get_phi g1  in
      match uu____9382 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9388 = get_phi g2  in
          (match uu____9388 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9400 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9400 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9431 =
                        FStar_TypeChecker_Env.binders_of_bindings r1  in
                      close_forall_no_univs1 uu____9431 phi1  in
                    let t2 =
                      let uu____9441 =
                        FStar_TypeChecker_Env.binders_of_bindings r2  in
                      close_forall_no_univs1 uu____9441 phi2  in
                    let uu____9450 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9450
                      (fun uu____9455  ->
                         let uu____9456 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9456
                           (fun uu____9463  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___412_9468 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9469 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___412_9468.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___412_9468.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___412_9468.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___412_9468.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9469;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___412_9468.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___412_9468.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___412_9468.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___412_9468.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___412_9468.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___412_9468.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___412_9468.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___412_9468.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___412_9468.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___412_9468.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___412_9468.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___412_9468.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___412_9468.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___412_9468.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___412_9468.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___412_9468.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___412_9468.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___412_9468.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___412_9468.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___412_9468.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___412_9468.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___412_9468.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___412_9468.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___412_9468.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___412_9468.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___412_9468.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___412_9468.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___412_9468.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___412_9468.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___412_9468.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___412_9468.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___412_9468.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___412_9468.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___412_9468.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___412_9468.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___412_9468.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9472 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9472
                                (fun goal  ->
                                   mlog
                                     (fun uu____9481  ->
                                        let uu____9482 =
                                          goal_to_string_verbose g1  in
                                        let uu____9483 =
                                          goal_to_string_verbose g2  in
                                        let uu____9484 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9482 uu____9483 uu____9484)
                                     (fun uu____9486  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9493  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9509 =
               set
                 (let uu___413_9514 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___413_9514.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___413_9514.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___413_9514.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___413_9514.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___413_9514.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___413_9514.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___413_9514.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___413_9514.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___413_9514.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___413_9514.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___413_9514.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___413_9514.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9509
               (fun uu____9517  ->
                  let uu____9518 = join_goals g1 g2  in
                  bind uu____9518 (fun g12  -> add_goals [g12]))
         | uu____9523 -> fail "join: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9532  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___414_9545 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___414_9545.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___414_9545.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___414_9545.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___414_9545.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___414_9545.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___414_9545.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___414_9545.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___414_9545.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___414_9545.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___414_9545.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___414_9545.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___414_9545.FStar_Tactics_Types.local_state)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9552  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9559 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9579 =
      let uu____9586 = cur_goal ()  in
      bind uu____9586
        (fun g  ->
           let uu____9596 =
             let uu____9605 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9605 t  in
           bind uu____9596
             (fun uu____9633  ->
                match uu____9633 with
                | (t1,typ,guard) ->
                    let uu____9649 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9649 with
                     | (hd1,args) ->
                         let uu____9698 =
                           let uu____9713 =
                             let uu____9714 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9714.FStar_Syntax_Syntax.n  in
                           (uu____9713, args)  in
                         (match uu____9698 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9735)::(q,uu____9737)::[]) when
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
                                let uu____9791 =
                                  let uu____9792 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9792
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9791
                                 in
                              let g2 =
                                let uu____9794 =
                                  let uu____9795 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9795
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9794
                                 in
                              bind __dismiss
                                (fun uu____9802  ->
                                   let uu____9803 = add_goals [g1; g2]  in
                                   bind uu____9803
                                     (fun uu____9812  ->
                                        let uu____9813 =
                                          let uu____9818 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9819 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9818, uu____9819)  in
                                        ret uu____9813))
                          | uu____9824 ->
                              let uu____9839 =
                                let uu____9840 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9840 typ  in
                              fail1 "Not a disjunction: %s" uu____9839))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9579
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9870 =
      let uu____9873 = cur_goal ()  in
      bind uu____9873
        (fun g  ->
           FStar_Options.push ();
           (let uu____9886 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9886);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___415_9893 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___415_9893.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___415_9893.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___415_9893.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9870
  
let (top_env : unit -> env tac) =
  fun uu____9905  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9918  ->
    let uu____9921 = cur_goal ()  in
    bind uu____9921
      (fun g  ->
         let uu____9927 =
           (FStar_Options.lax ()) ||
             (let uu____9929 = FStar_Tactics_Types.goal_env g  in
              uu____9929.FStar_TypeChecker_Env.lax)
            in
         ret uu____9927)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9944 =
        mlog
          (fun uu____9949  ->
             let uu____9950 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9950)
          (fun uu____9953  ->
             let uu____9954 = cur_goal ()  in
             bind uu____9954
               (fun goal  ->
                  let env =
                    let uu____9962 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9962 ty  in
                  let uu____9963 = __tc env tm  in
                  bind uu____9963
                    (fun uu____9982  ->
                       match uu____9982 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9996  ->
                                let uu____9997 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9997)
                             (fun uu____9999  ->
                                mlog
                                  (fun uu____10002  ->
                                     let uu____10003 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10003)
                                  (fun uu____10006  ->
                                     let uu____10007 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10007
                                       (fun uu____10011  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9944
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10034 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10040 =
              let uu____10047 =
                let uu____10048 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10048
                 in
              new_uvar "uvar_env.2" env uu____10047  in
            bind uu____10040
              (fun uu____10064  ->
                 match uu____10064 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10034
        (fun typ  ->
           let uu____10076 = new_uvar "uvar_env" env typ  in
           bind uu____10076
             (fun uu____10090  ->
                match uu____10090 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10108 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10127 -> g.FStar_Tactics_Types.opts
             | uu____10130 -> FStar_Options.peek ()  in
           let uu____10133 = FStar_Syntax_Util.head_and_args t  in
           match uu____10133 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10153);
                FStar_Syntax_Syntax.pos = uu____10154;
                FStar_Syntax_Syntax.vars = uu____10155;_},uu____10156)
               ->
               let env1 =
                 let uu___416_10198 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___416_10198.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___416_10198.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___416_10198.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___416_10198.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___416_10198.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___416_10198.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___416_10198.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___416_10198.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___416_10198.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___416_10198.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___416_10198.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___416_10198.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___416_10198.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___416_10198.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___416_10198.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___416_10198.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___416_10198.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___416_10198.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___416_10198.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___416_10198.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___416_10198.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___416_10198.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___416_10198.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___416_10198.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___416_10198.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___416_10198.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___416_10198.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___416_10198.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___416_10198.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___416_10198.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___416_10198.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___416_10198.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___416_10198.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___416_10198.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___416_10198.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___416_10198.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___416_10198.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___416_10198.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___416_10198.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___416_10198.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___416_10198.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10200 =
                 let uu____10203 = bnorm_goal g  in [uu____10203]  in
               add_goals uu____10200
           | uu____10204 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10108
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10253 = if b then t2 else ret false  in
             bind uu____10253 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10264 = trytac comp  in
      bind uu____10264
        (fun uu___351_10272  ->
           match uu___351_10272 with
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
        let uu____10298 =
          bind get
            (fun ps  ->
               let uu____10304 = __tc e t1  in
               bind uu____10304
                 (fun uu____10324  ->
                    match uu____10324 with
                    | (t11,ty1,g1) ->
                        let uu____10336 = __tc e t2  in
                        bind uu____10336
                          (fun uu____10356  ->
                             match uu____10356 with
                             | (t21,ty2,g2) ->
                                 let uu____10368 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10368
                                   (fun uu____10373  ->
                                      let uu____10374 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10374
                                        (fun uu____10380  ->
                                           let uu____10381 =
                                             do_unify e ty1 ty2  in
                                           let uu____10384 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10381 uu____10384)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10298
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10417  ->
             let uu____10418 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10418
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
        (fun uu____10439  ->
           let uu____10440 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10440)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10450 =
      mlog
        (fun uu____10455  ->
           let uu____10456 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10456)
        (fun uu____10459  ->
           let uu____10460 = cur_goal ()  in
           bind uu____10460
             (fun g  ->
                let uu____10466 =
                  let uu____10475 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10475 ty  in
                bind uu____10466
                  (fun uu____10487  ->
                     match uu____10487 with
                     | (ty1,uu____10497,guard) ->
                         let uu____10499 =
                           let uu____10502 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10502 guard  in
                         bind uu____10499
                           (fun uu____10505  ->
                              let uu____10506 =
                                let uu____10509 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10510 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10509 uu____10510 ty1  in
                              bind uu____10506
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10516 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10516
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10522 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10523 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10522
                                          uu____10523
                                         in
                                      let nty =
                                        let uu____10525 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10525 ty1  in
                                      let uu____10526 =
                                        let uu____10529 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10529 ng nty  in
                                      bind uu____10526
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10535 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10535
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10450
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10598 =
      let uu____10607 = cur_goal ()  in
      bind uu____10607
        (fun g  ->
           let uu____10619 =
             let uu____10628 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10628 s_tm  in
           bind uu____10619
             (fun uu____10646  ->
                match uu____10646 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10664 =
                      let uu____10667 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10667 guard  in
                    bind uu____10664
                      (fun uu____10679  ->
                         let uu____10680 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10680 with
                         | (h,args) ->
                             let uu____10725 =
                               let uu____10732 =
                                 let uu____10733 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10733.FStar_Syntax_Syntax.n  in
                               match uu____10732 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10748;
                                      FStar_Syntax_Syntax.vars = uu____10749;_},us)
                                   -> ret (fv, us)
                               | uu____10759 -> fail "type is not an fv"  in
                             bind uu____10725
                               (fun uu____10779  ->
                                  match uu____10779 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10795 =
                                        let uu____10798 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10798 t_lid
                                         in
                                      (match uu____10795 with
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
                                                  (fun uu____10847  ->
                                                     let uu____10848 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10848 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10863 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10891
                                                                  =
                                                                  let uu____10894
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10894
                                                                    c_lid
                                                                   in
                                                                match uu____10891
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
                                                                    uu____10964
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
                                                                    let uu____10969
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10969
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10992
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10992
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11035
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11035
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11108
                                                                    =
                                                                    let uu____11109
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11109
                                                                     in
                                                                    failwhen
                                                                    uu____11108
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11126
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
                                                                    uu___352_11142
                                                                    =
                                                                    match uu___352_11142
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11145)
                                                                    -> true
                                                                    | 
                                                                    uu____11146
                                                                    -> false
                                                                     in
                                                                    let uu____11149
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11149
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
                                                                    uu____11282
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
                                                                    uu____11344
                                                                     ->
                                                                    match uu____11344
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11364),
                                                                    (t,uu____11366))
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
                                                                    uu____11434
                                                                     ->
                                                                    match uu____11434
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11460),
                                                                    (t,uu____11462))
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
                                                                    uu____11517
                                                                     ->
                                                                    match uu____11517
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
                                                                    let uu____11567
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___417_11584
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___417_11584.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11567
                                                                    with
                                                                    | 
                                                                    (uu____11597,uu____11598,uu____11599,pat_t,uu____11601,uu____11602)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11608
                                                                    =
                                                                    let uu____11609
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11609
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11608
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11613
                                                                    =
                                                                    let uu____11622
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11622]
                                                                     in
                                                                    let uu____11641
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11613
                                                                    uu____11641
                                                                     in
                                                                    let nty =
                                                                    let uu____11647
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11647
                                                                     in
                                                                    let uu____11650
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11650
                                                                    (fun
                                                                    uu____11679
                                                                     ->
                                                                    match uu____11679
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
                                                                    let uu____11705
                                                                    =
                                                                    let uu____11716
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11716]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11705
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11752
                                                                    =
                                                                    let uu____11763
                                                                    =
                                                                    let uu____11768
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11768)
                                                                     in
                                                                    (g', br,
                                                                    uu____11763)
                                                                     in
                                                                    ret
                                                                    uu____11752))))))
                                                                    | 
                                                                    uu____11789
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10863
                                                           (fun goal_brs  ->
                                                              let uu____11838
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11838
                                                              with
                                                              | (goals1,brs,infos)
                                                                  ->
                                                                  let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    (s_tm1,
                                                                    brs))
                                                                    FStar_Pervasives_Native.None
                                                                    s_tm1.FStar_Syntax_Syntax.pos
                                                                     in
                                                                  let uu____11911
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11911
                                                                    (
                                                                    fun
                                                                    uu____11922
                                                                     ->
                                                                    let uu____11923
                                                                    =
                                                                    add_goals
                                                                    goals1
                                                                     in
                                                                    bind
                                                                    uu____11923
                                                                    (fun
                                                                    uu____11933
                                                                     ->
                                                                    ret infos))))
                                            | uu____11940 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10598
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11985::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12013 = init xs  in x :: uu____12013
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12025 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12034) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12099 = last args  in
          (match uu____12099 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12129 =
                 let uu____12130 =
                   let uu____12135 =
                     let uu____12136 =
                       let uu____12141 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12141  in
                     uu____12136 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12135, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12130  in
               FStar_All.pipe_left ret uu____12129)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12154,uu____12155) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12207 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12207 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12248 =
                      let uu____12249 =
                        let uu____12254 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12254)  in
                      FStar_Reflection_Data.Tv_Abs uu____12249  in
                    FStar_All.pipe_left ret uu____12248))
      | FStar_Syntax_Syntax.Tm_type uu____12257 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12281 ->
          let uu____12296 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12296 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12326 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12326 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12379 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12391 =
            let uu____12392 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12392  in
          FStar_All.pipe_left ret uu____12391
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12413 =
            let uu____12414 =
              let uu____12419 =
                let uu____12420 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12420  in
              (uu____12419, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12414  in
          FStar_All.pipe_left ret uu____12413
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12454 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12459 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12459 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12512 ->
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
             | FStar_Util.Inr uu____12546 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12550 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12550 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12570 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12574 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12628 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12628
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12647 =
                  let uu____12654 =
                    FStar_List.map
                      (fun uu____12666  ->
                         match uu____12666 with
                         | (p1,uu____12674) -> inspect_pat p1) ps
                     in
                  (fv, uu____12654)  in
                FStar_Reflection_Data.Pat_Cons uu____12647
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
              (fun uu___353_12768  ->
                 match uu___353_12768 with
                 | (pat,uu____12790,t5) ->
                     let uu____12808 = inspect_pat pat  in (uu____12808, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12817 ->
          ((let uu____12819 =
              let uu____12824 =
                let uu____12825 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12826 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12825 uu____12826
                 in
              (FStar_Errors.Warning_CantInspect, uu____12824)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12819);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12025
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12839 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12839
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12843 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12843
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12847 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12847
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12854 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12854
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12879 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12879
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12896 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12896
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12915 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12915
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12919 =
          let uu____12920 =
            let uu____12927 =
              let uu____12928 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12928  in
            FStar_Syntax_Syntax.mk uu____12927  in
          uu____12920 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12919
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12936 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12936
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12945 =
          let uu____12946 =
            let uu____12953 =
              let uu____12954 =
                let uu____12967 =
                  let uu____12970 =
                    let uu____12971 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12971]  in
                  FStar_Syntax_Subst.close uu____12970 t2  in
                ((false, [lb]), uu____12967)  in
              FStar_Syntax_Syntax.Tm_let uu____12954  in
            FStar_Syntax_Syntax.mk uu____12953  in
          uu____12946 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12945
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13011 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13011 with
         | (lbs,body) ->
             let uu____13026 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13026)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13060 =
                let uu____13061 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13061  in
              FStar_All.pipe_left wrap uu____13060
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13068 =
                let uu____13069 =
                  let uu____13082 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13098 = pack_pat p1  in
                         (uu____13098, false)) ps
                     in
                  (fv, uu____13082)  in
                FStar_Syntax_Syntax.Pat_cons uu____13069  in
              FStar_All.pipe_left wrap uu____13068
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
            (fun uu___354_13144  ->
               match uu___354_13144 with
               | (pat,t1) ->
                   let uu____13161 = pack_pat pat  in
                   (uu____13161, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13209 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13209
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13237 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13237
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13283 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13283
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13322 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13322
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13339 =
        bind get
          (fun ps  ->
             let uu____13345 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13345 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13339
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13374 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___418_13381 = ps  in
                 let uu____13382 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___418_13381.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___418_13381.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___418_13381.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___418_13381.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___418_13381.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___418_13381.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___418_13381.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___418_13381.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___418_13381.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___418_13381.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___418_13381.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___418_13381.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13382
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13374
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13407 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13407 with
      | (u,ctx_uvars,g_u) ->
          let uu____13439 = FStar_List.hd ctx_uvars  in
          (match uu____13439 with
           | (ctx_uvar,uu____13453) ->
               let g =
                 let uu____13455 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13455 false
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
        let uu____13475 = goal_of_goal_ty env typ  in
        match uu____13475 with
        | (g,g_u) ->
            let ps =
              let uu____13487 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13488 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13487;
                FStar_Tactics_Types.local_state = uu____13488
              }  in
            let uu____13495 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13495)
  