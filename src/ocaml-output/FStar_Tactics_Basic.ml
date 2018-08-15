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
      let uu____151 = FStar_Options.tactics_failhard ()  in
      if uu____151
      then run t p
      else
        (try (fun uu___356_158  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____167,msg) ->
             FStar_Tactics_Result.Failed (msg, p)
         | FStar_Errors.Error (uu____169,msg,uu____171) ->
             FStar_Tactics_Result.Failed (msg, p)
         | e ->
             let uu____173 =
               let uu____178 = FStar_Util.message_of_exn e  in (uu____178, p)
                in
             FStar_Tactics_Result.Failed uu____173)
  
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
           let uu____250 = run t1 p  in
           match uu____250 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____257 = t2 a  in run uu____257 q
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
    let uu____277 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____277 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____295 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____296 =
      let uu____297 = check_goal_solved g  in
      match uu____297 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____301 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____301
       in
    FStar_Util.format2 "%s%s" uu____295 uu____296
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____312 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____312
      then goal_to_string_verbose g
      else
        (let w =
           let uu____315 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____315 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____319 = FStar_Tactics_Types.goal_env g  in
               tts uu____319 t
            in
         let uu____320 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____321 =
           let uu____322 = FStar_Tactics_Types.goal_env g  in
           tts uu____322
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____320 w uu____321)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____338 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____338
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____354 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____354
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____375 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____375
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____382) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____392) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____411 =
      let uu____412 = FStar_Tactics_Types.goal_env g  in
      let uu____413 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____412 uu____413  in
    FStar_Syntax_Util.un_squash uu____411
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____419 = get_phi g  in FStar_Option.isSome uu____419 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____438  ->
    bind get
      (fun ps  ->
         let uu____444 =
           let uu____445 =
             FStar_Ident.string_of_lid
               (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
              in
           FStar_Options.debug_module uu____445  in
         ret uu____444)
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____457 = goal_to_string ps goal  in tacprint uu____457
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____469 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____473 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____473))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____482  ->
    match uu____482 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____495 =
          let uu____498 =
            let uu____499 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____499 msg
             in
          let uu____500 =
            let uu____503 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____504 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____504
              else ""  in
            let uu____506 =
              let uu____509 =
                let uu____510 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____510
                then
                  let uu____511 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____511
                else ""  in
              let uu____513 =
                let uu____516 =
                  let uu____517 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____518 =
                    let uu____519 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____519  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____517
                    uu____518
                   in
                let uu____522 =
                  let uu____525 =
                    let uu____526 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____527 =
                      let uu____528 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____528  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____526
                      uu____527
                     in
                  [uu____525]  in
                uu____516 :: uu____522  in
              uu____509 :: uu____513  in
            uu____503 :: uu____506  in
          uu____498 :: uu____500  in
        FStar_String.concat "" uu____495
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____537 =
        let uu____538 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____538  in
      let uu____539 =
        let uu____544 =
          let uu____545 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____545  in
        FStar_Syntax_Print.binders_to_json uu____544  in
      FStar_All.pipe_right uu____537 uu____539  in
    let uu____546 =
      let uu____553 =
        let uu____560 =
          let uu____565 =
            let uu____566 =
              let uu____573 =
                let uu____578 =
                  let uu____579 =
                    let uu____580 = FStar_Tactics_Types.goal_env g  in
                    let uu____581 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____580 uu____581  in
                  FStar_Util.JsonStr uu____579  in
                ("witness", uu____578)  in
              let uu____582 =
                let uu____589 =
                  let uu____594 =
                    let uu____595 =
                      let uu____596 = FStar_Tactics_Types.goal_env g  in
                      let uu____597 = FStar_Tactics_Types.goal_type g  in
                      tts uu____596 uu____597  in
                    FStar_Util.JsonStr uu____595  in
                  ("type", uu____594)  in
                [uu____589]  in
              uu____573 :: uu____582  in
            FStar_Util.JsonAssoc uu____566  in
          ("goal", uu____565)  in
        [uu____560]  in
      ("hyps", g_binders) :: uu____553  in
    FStar_Util.JsonAssoc uu____546
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____630  ->
    match uu____630 with
    | (msg,ps) ->
        let uu____637 =
          let uu____644 =
            let uu____651 =
              let uu____658 =
                let uu____665 =
                  let uu____670 =
                    let uu____671 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____671  in
                  ("goals", uu____670)  in
                let uu____674 =
                  let uu____681 =
                    let uu____686 =
                      let uu____687 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____687  in
                    ("smt-goals", uu____686)  in
                  [uu____681]  in
                uu____665 :: uu____674  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____658
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____651  in
          let uu____710 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____723 =
                let uu____728 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____728)  in
              [uu____723]
            else []  in
          FStar_List.append uu____644 uu____710  in
        FStar_Util.JsonAssoc uu____637
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____758  ->
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
         (let uu____781 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____781 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____799 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____799 msg);
         FStar_Tactics_Result.Success ((), ps))
  
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
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
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
                 let uu___357_1033 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___357_1033.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___357_1033.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___357_1033.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___357_1033.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___357_1033.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___357_1033.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___357_1033.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___357_1033.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___357_1033.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___357_1033.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___357_1033.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___357_1033.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1060 = catch t  in
    bind uu____1060
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1087 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___359_1118  ->
              match () with
              | () -> let uu____1123 = trytac t  in run uu____1123 ps) ()
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
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___360_1219 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1219.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1219.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1219.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1219.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1219.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1219.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1219.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1219.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1219.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1219.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1219.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___360_1219.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1240 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1240
         then
           let uu____1241 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1242 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1241
             uu____1242
         else ());
        (try
           (fun uu___362_1249  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1256 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1256
                    then
                      let uu____1257 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1258 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1259 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1257
                        uu____1258 uu____1259
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1264 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1264 (fun uu____1268  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1275,msg) ->
             mlog
               (fun uu____1278  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1280  -> ret false)
         | FStar_Errors.Error (uu____1281,msg,r) ->
             mlog
               (fun uu____1286  ->
                  let uu____1287 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1287) (fun uu____1289  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___363_1300 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___363_1300.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___363_1300.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___363_1300.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___364_1303 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_1303.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___364_1303.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___364_1303.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___364_1303.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_1303.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_1303.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_1303.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_1303.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_1303.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_1303.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_1303.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___364_1303.FStar_Tactics_Types.local_state)
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
          (fun uu____1326  ->
             (let uu____1328 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1328
              then
                (FStar_Options.push ();
                 (let uu____1330 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1332 = __do_unify env t1 t2  in
              bind uu____1332
                (fun r  ->
                   (let uu____1339 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1339 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1342  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___365_1349 = ps  in
         let uu____1350 =
           FStar_List.filter
             (fun g  ->
                let uu____1356 = check_goal_solved g  in
                FStar_Option.isNone uu____1356) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___365_1349.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___365_1349.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___365_1349.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1350;
           FStar_Tactics_Types.smt_goals =
             (uu___365_1349.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___365_1349.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___365_1349.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___365_1349.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___365_1349.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___365_1349.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___365_1349.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___365_1349.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___365_1349.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1373 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1373 with
      | FStar_Pervasives_Native.Some uu____1378 ->
          let uu____1379 =
            let uu____1380 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1380  in
          fail uu____1379
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1396 = FStar_Tactics_Types.goal_env goal  in
      let uu____1397 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1396 solution uu____1397
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1403 =
         let uu___366_1404 = p  in
         let uu____1405 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___366_1404.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___366_1404.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___366_1404.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1405;
           FStar_Tactics_Types.smt_goals =
             (uu___366_1404.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___366_1404.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___366_1404.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___366_1404.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___366_1404.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___366_1404.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___366_1404.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___366_1404.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___366_1404.FStar_Tactics_Types.local_state)
         }  in
       set uu____1403)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1426  ->
           let uu____1427 =
             let uu____1428 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1428  in
           let uu____1429 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1427 uu____1429)
        (fun uu____1432  ->
           let uu____1433 = trysolve goal solution  in
           bind uu____1433
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1441  -> remove_solved_goals)
                else
                  (let uu____1443 =
                     let uu____1444 =
                       let uu____1445 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1445 solution  in
                     let uu____1446 =
                       let uu____1447 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1448 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1447 uu____1448  in
                     let uu____1449 =
                       let uu____1450 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1451 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1450 uu____1451  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1444 uu____1446 uu____1449
                      in
                   fail uu____1443)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1466 = set_solution goal solution  in
      bind uu____1466
        (fun uu____1470  ->
           bind __dismiss (fun uu____1472  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___367_1490 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_1490.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_1490.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_1490.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___367_1490.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___367_1490.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_1490.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_1490.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_1490.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_1490.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_1490.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_1490.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___367_1490.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___368_1508 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1508.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1508.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1508.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___368_1508.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___368_1508.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1508.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1508.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1508.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___368_1508.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___368_1508.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_1508.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___368_1508.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1529 = FStar_Options.defensive ()  in
    if uu____1529
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1534 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1534)
         in
      let b2 =
        b1 &&
          (let uu____1537 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1537)
         in
      let rec aux b3 e =
        let uu____1549 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1549 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1567 =
        (let uu____1570 = aux b2 env  in Prims.op_Negation uu____1570) &&
          (let uu____1572 = FStar_ST.op_Bang nwarn  in
           uu____1572 < (Prims.parse_int "5"))
         in
      (if uu____1567
       then
         ((let uu____1593 =
             let uu____1594 = FStar_Tactics_Types.goal_type g  in
             uu____1594.FStar_Syntax_Syntax.pos  in
           let uu____1597 =
             let uu____1602 =
               let uu____1603 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1603
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1602)  in
           FStar_Errors.log_issue uu____1593 uu____1597);
          (let uu____1604 =
             let uu____1605 = FStar_ST.op_Bang nwarn  in
             uu____1605 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1604))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1665 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1665.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1665.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1665.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___369_1665.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1665.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1665.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1665.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1665.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1665.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1665.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1665.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___369_1665.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___370_1685 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1685.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1685.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1685.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_1685.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1685.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1685.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1685.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1685.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1685.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1685.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1685.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1685.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___371_1705 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1705.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1705.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1705.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___371_1705.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___371_1705.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1705.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1705.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1705.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1705.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1705.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1705.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1705.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___372_1725 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1725.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1725.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_1725.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___372_1725.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___372_1725.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1725.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1725.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1725.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_1725.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_1725.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_1725.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_1725.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1736  -> add_goals [g]) 
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
        let uu____1764 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1764 with
        | (u,ctx_uvar,g_u) ->
            let uu____1798 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1798
              (fun uu____1807  ->
                 let uu____1808 =
                   let uu____1813 =
                     let uu____1814 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1814  in
                   (u, uu____1813)  in
                 ret uu____1808)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1832 = FStar_Syntax_Util.un_squash t  in
    match uu____1832 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1842 =
          let uu____1843 = FStar_Syntax_Subst.compress t'  in
          uu____1843.FStar_Syntax_Syntax.n  in
        (match uu____1842 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1847 -> false)
    | uu____1848 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1858 = FStar_Syntax_Util.un_squash t  in
    match uu____1858 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1868 =
          let uu____1869 = FStar_Syntax_Subst.compress t'  in
          uu____1869.FStar_Syntax_Syntax.n  in
        (match uu____1868 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1873 -> false)
    | uu____1874 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1885  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1896 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1896 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1903 = goal_to_string_verbose hd1  in
                    let uu____1904 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1903 uu____1904);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____1914 =
      bind get
        (fun ps  ->
           let uu____1920 = cur_goal ()  in
           bind uu____1920
             (fun g  ->
                (let uu____1927 =
                   let uu____1928 = FStar_Tactics_Types.goal_type g  in
                   uu____1928.FStar_Syntax_Syntax.pos  in
                 let uu____1931 =
                   let uu____1936 =
                     let uu____1937 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1937
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1936)  in
                 FStar_Errors.log_issue uu____1927 uu____1931);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____1914
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1948  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___373_1958 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___373_1958.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___373_1958.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___373_1958.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___373_1958.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___373_1958.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___373_1958.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___373_1958.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___373_1958.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___373_1958.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___373_1958.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___373_1958.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___373_1958.FStar_Tactics_Types.local_state)
           }  in
         let uu____1959 = set ps1  in
         bind uu____1959
           (fun uu____1964  ->
              let uu____1965 = FStar_BigInt.of_int_fs n1  in ret uu____1965))
  
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
            let uu____1993 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1993 phi  in
          let uu____1994 = new_uvar reason env typ  in
          bind uu____1994
            (fun uu____2009  ->
               match uu____2009 with
               | (uu____2016,ctx_uvar) ->
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
             (fun uu____2061  ->
                let uu____2062 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2062)
             (fun uu____2065  ->
                let e1 =
                  let uu___374_2067 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___374_2067.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___374_2067.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___374_2067.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___374_2067.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___374_2067.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___374_2067.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___374_2067.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___374_2067.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___374_2067.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___374_2067.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___374_2067.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___374_2067.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___374_2067.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___374_2067.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___374_2067.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___374_2067.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___374_2067.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___374_2067.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___374_2067.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___374_2067.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___374_2067.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___374_2067.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___374_2067.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___374_2067.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___374_2067.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___374_2067.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___374_2067.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___374_2067.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___374_2067.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___374_2067.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___374_2067.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___374_2067.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___374_2067.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___374_2067.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___374_2067.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___374_2067.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___374_2067.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___374_2067.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___374_2067.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___374_2067.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___374_2067.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___376_2078  ->
                     match () with
                     | () ->
                         let uu____2087 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2087) ()
                with
                | FStar_Errors.Err (uu____2114,msg) ->
                    let uu____2116 = tts e1 t  in
                    let uu____2117 =
                      let uu____2118 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2118
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2116 uu____2117 msg
                | FStar_Errors.Error (uu____2125,msg,uu____2127) ->
                    let uu____2128 = tts e1 t  in
                    let uu____2129 =
                      let uu____2130 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2130
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2128 uu____2129 msg))
  
let (__tc_ghost :
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
             (fun uu____2179  ->
                let uu____2180 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2180)
             (fun uu____2183  ->
                let e1 =
                  let uu___377_2185 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___377_2185.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___377_2185.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___377_2185.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___377_2185.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___377_2185.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___377_2185.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___377_2185.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___377_2185.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___377_2185.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___377_2185.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___377_2185.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___377_2185.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___377_2185.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___377_2185.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___377_2185.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___377_2185.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___377_2185.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___377_2185.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___377_2185.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___377_2185.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___377_2185.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___377_2185.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___377_2185.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___377_2185.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___377_2185.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___377_2185.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___377_2185.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___377_2185.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___377_2185.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___377_2185.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___377_2185.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___377_2185.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___377_2185.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___377_2185.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___377_2185.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___377_2185.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___377_2185.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___377_2185.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___377_2185.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___377_2185.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___377_2185.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___379_2199  ->
                     match () with
                     | () ->
                         let uu____2208 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2208 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2246,msg) ->
                    let uu____2248 = tts e1 t  in
                    let uu____2249 =
                      let uu____2250 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2250
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2248 uu____2249 msg
                | FStar_Errors.Error (uu____2257,msg,uu____2259) ->
                    let uu____2260 = tts e1 t  in
                    let uu____2261 =
                      let uu____2262 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2262
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2260 uu____2261 msg))
  
let (__tc_lax :
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
             (fun uu____2311  ->
                let uu____2312 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2312)
             (fun uu____2316  ->
                let e1 =
                  let uu___380_2318 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___380_2318.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___380_2318.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___380_2318.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___380_2318.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___380_2318.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___380_2318.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___380_2318.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___380_2318.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___380_2318.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___380_2318.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___380_2318.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___380_2318.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___380_2318.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___380_2318.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___380_2318.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___380_2318.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___380_2318.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___380_2318.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___380_2318.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___380_2318.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___380_2318.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___380_2318.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___380_2318.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___380_2318.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___380_2318.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___380_2318.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___380_2318.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___380_2318.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___380_2318.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___380_2318.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___380_2318.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___380_2318.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___380_2318.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___380_2318.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___380_2318.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___380_2318.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___380_2318.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___380_2318.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___380_2318.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___380_2318.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___380_2318.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___381_2320 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___381_2320.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___381_2320.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___381_2320.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___381_2320.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___381_2320.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___381_2320.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___381_2320.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___381_2320.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___381_2320.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___381_2320.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___381_2320.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___381_2320.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___381_2320.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___381_2320.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___381_2320.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___381_2320.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___381_2320.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___381_2320.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___381_2320.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___381_2320.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___381_2320.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___381_2320.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___381_2320.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___381_2320.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___381_2320.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___381_2320.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___381_2320.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___381_2320.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___381_2320.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___381_2320.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___381_2320.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___381_2320.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___381_2320.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___381_2320.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___381_2320.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___381_2320.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___381_2320.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___381_2320.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___381_2320.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___381_2320.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___381_2320.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___383_2334  ->
                     match () with
                     | () ->
                         let uu____2343 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2343 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2381,msg) ->
                    let uu____2383 = tts e2 t  in
                    let uu____2384 =
                      let uu____2385 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2385
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2383 uu____2384 msg
                | FStar_Errors.Error (uu____2392,msg,uu____2394) ->
                    let uu____2395 = tts e2 t  in
                    let uu____2396 =
                      let uu____2397 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2397
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2395 uu____2396 msg))
  
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
  fun uu____2424  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___384_2442 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___384_2442.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___384_2442.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___384_2442.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___384_2442.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___384_2442.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___384_2442.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___384_2442.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___384_2442.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___384_2442.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___384_2442.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___384_2442.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___384_2442.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2466 = get_guard_policy ()  in
      bind uu____2466
        (fun old_pol  ->
           let uu____2472 = set_guard_policy pol  in
           bind uu____2472
             (fun uu____2476  ->
                bind t
                  (fun r  ->
                     let uu____2480 = set_guard_policy old_pol  in
                     bind uu____2480 (fun uu____2484  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2487 = let uu____2492 = cur_goal ()  in trytac uu____2492  in
  bind uu____2487
    (fun uu___347_2499  ->
       match uu___347_2499 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2505 = FStar_Options.peek ()  in ret uu____2505)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2527  ->
             let uu____2528 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2528)
          (fun uu____2531  ->
             let uu____2532 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2532
               (fun uu____2536  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2540 =
                         let uu____2541 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2541.FStar_TypeChecker_Env.guard_f  in
                       match uu____2540 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2545 = istrivial e f  in
                           if uu____2545
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2555 =
                                          let uu____2560 =
                                            let uu____2561 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2561
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2560)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2555);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2564  ->
                                           let uu____2565 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2565)
                                        (fun uu____2568  ->
                                           let uu____2569 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2569
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___385_2576 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___385_2576.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___385_2576.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___385_2576.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2579  ->
                                           let uu____2580 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2580)
                                        (fun uu____2583  ->
                                           let uu____2584 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2584
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___386_2591 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___386_2591.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___386_2591.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___386_2591.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2594  ->
                                           let uu____2595 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2595)
                                        (fun uu____2597  ->
                                           try
                                             (fun uu___388_2602  ->
                                                match () with
                                                | () ->
                                                    let uu____2605 =
                                                      let uu____2606 =
                                                        let uu____2607 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2607
                                                         in
                                                      Prims.op_Negation
                                                        uu____2606
                                                       in
                                                    if uu____2605
                                                    then
                                                      mlog
                                                        (fun uu____2612  ->
                                                           let uu____2613 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2613)
                                                        (fun uu____2615  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___387_2618 ->
                                               mlog
                                                 (fun uu____2623  ->
                                                    let uu____2624 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2624)
                                                 (fun uu____2626  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2636 =
      let uu____2639 = cur_goal ()  in
      bind uu____2639
        (fun goal  ->
           let uu____2645 =
             let uu____2654 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____2654 t  in
           bind uu____2645
             (fun uu____2665  ->
                match uu____2665 with
                | (uu____2674,typ,uu____2676) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2636
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2705 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2705 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2716  ->
    let uu____2719 = cur_goal ()  in
    bind uu____2719
      (fun goal  ->
         let uu____2725 =
           let uu____2726 = FStar_Tactics_Types.goal_env goal  in
           let uu____2727 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2726 uu____2727  in
         if uu____2725
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2731 =
              let uu____2732 = FStar_Tactics_Types.goal_env goal  in
              let uu____2733 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2732 uu____2733  in
            fail1 "Not a trivial goal: %s" uu____2731))
  
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
          let uu____2762 =
            let uu____2763 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2763.FStar_TypeChecker_Env.guard_f  in
          match uu____2762 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2771 = istrivial e f  in
              if uu____2771
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2779 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2779
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___389_2789 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___389_2789.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___389_2789.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___389_2789.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
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
             let uu____2838 =
               try
                 (fun uu___394_2861  ->
                    match () with
                    | () ->
                        let uu____2872 =
                          let uu____2881 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2881
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2872) ()
               with | uu___393_2891 -> fail "divide: not enough goals"  in
             bind uu____2838
               (fun uu____2927  ->
                  match uu____2927 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___390_2953 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___390_2953.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___390_2953.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___390_2953.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___390_2953.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___390_2953.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___390_2953.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___390_2953.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___390_2953.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___390_2953.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___390_2953.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___390_2953.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2954 = set lp  in
                      bind uu____2954
                        (fun uu____2962  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___391_2978 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___391_2978.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___391_2978.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___391_2978.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___391_2978.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___391_2978.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___391_2978.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___391_2978.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___391_2978.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___391_2978.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___391_2978.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___391_2978.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2979 = set rp  in
                                     bind uu____2979
                                       (fun uu____2987  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___392_3003 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___392_3003.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___392_3003.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3004 = set p'
                                                       in
                                                    bind uu____3004
                                                      (fun uu____3012  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3018 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3039 = divide FStar_BigInt.one f idtac  in
    bind uu____3039
      (fun uu____3052  -> match uu____3052 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3089::uu____3090 ->
             let uu____3093 =
               let uu____3102 = map tau  in
               divide FStar_BigInt.one tau uu____3102  in
             bind uu____3093
               (fun uu____3120  ->
                  match uu____3120 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3161 =
        bind t1
          (fun uu____3166  ->
             let uu____3167 = map t2  in
             bind uu____3167 (fun uu____3175  -> ret ()))
         in
      focus uu____3161
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3184  ->
    let uu____3187 =
      let uu____3190 = cur_goal ()  in
      bind uu____3190
        (fun goal  ->
           let uu____3199 =
             let uu____3206 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3206  in
           match uu____3199 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3215 =
                 let uu____3216 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3216  in
               if uu____3215
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3221 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3221 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3235 = new_uvar "intro" env' typ'  in
                  bind uu____3235
                    (fun uu____3251  ->
                       match uu____3251 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3275 = set_solution goal sol  in
                           bind uu____3275
                             (fun uu____3281  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3283 =
                                  let uu____3286 = bnorm_goal g  in
                                  replace_cur uu____3286  in
                                bind uu____3283 (fun uu____3288  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3293 =
                 let uu____3294 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3295 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3294 uu____3295  in
               fail1 "goal is not an arrow (%s)" uu____3293)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3187
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3310  ->
    let uu____3317 = cur_goal ()  in
    bind uu____3317
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3334 =
            let uu____3341 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3341  in
          match uu____3334 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3354 =
                let uu____3355 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3355  in
              if uu____3354
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3368 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3368
                    in
                 let bs =
                   let uu____3378 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3378; b]  in
                 let env' =
                   let uu____3404 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3404 bs  in
                 let uu____3405 =
                   let uu____3412 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3412  in
                 bind uu____3405
                   (fun uu____3431  ->
                      match uu____3431 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3445 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3448 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3445
                              FStar_Parser_Const.effect_Tot_lid uu____3448 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3466 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3466 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3488 =
                                   let uu____3489 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3489.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3488
                                  in
                               let uu____3502 = set_solution goal tm  in
                               bind uu____3502
                                 (fun uu____3511  ->
                                    let uu____3512 =
                                      let uu____3515 =
                                        bnorm_goal
                                          (let uu___395_3518 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___395_3518.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___395_3518.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___395_3518.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3515  in
                                    bind uu____3512
                                      (fun uu____3525  ->
                                         let uu____3526 =
                                           let uu____3531 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3531, b)  in
                                         ret uu____3526)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3540 =
                let uu____3541 = FStar_Tactics_Types.goal_env goal  in
                let uu____3542 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3541 uu____3542  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3540))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3560 = cur_goal ()  in
    bind uu____3560
      (fun goal  ->
         mlog
           (fun uu____3567  ->
              let uu____3568 =
                let uu____3569 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3569  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3568)
           (fun uu____3574  ->
              let steps =
                let uu____3578 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3578
                 in
              let t =
                let uu____3582 = FStar_Tactics_Types.goal_env goal  in
                let uu____3583 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3582 uu____3583  in
              let uu____3584 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3584))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3608 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____3616 -> g.FStar_Tactics_Types.opts
                 | uu____3619 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____3624  ->
                    let uu____3625 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3625)
                 (fun uu____3628  ->
                    let uu____3629 = __tc_lax e t  in
                    bind uu____3629
                      (fun uu____3650  ->
                         match uu____3650 with
                         | (t1,uu____3660,uu____3661) ->
                             let steps =
                               let uu____3665 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3665
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____3671  ->
                                  let uu____3672 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3672)
                               (fun uu____3674  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3608
  
let (refine_intro : unit -> unit tac) =
  fun uu____3685  ->
    let uu____3688 =
      let uu____3691 = cur_goal ()  in
      bind uu____3691
        (fun g  ->
           let uu____3698 =
             let uu____3709 = FStar_Tactics_Types.goal_env g  in
             let uu____3710 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3709 uu____3710
              in
           match uu____3698 with
           | (uu____3713,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3738 =
                 let uu____3743 =
                   let uu____3748 =
                     let uu____3749 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3749]  in
                   FStar_Syntax_Subst.open_term uu____3748 phi  in
                 match uu____3743 with
                 | (bvs,phi1) ->
                     let uu____3774 =
                       let uu____3775 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3775  in
                     (uu____3774, phi1)
                  in
               (match uu____3738 with
                | (bv1,phi1) ->
                    let uu____3794 =
                      let uu____3797 = FStar_Tactics_Types.goal_env g  in
                      let uu____3798 =
                        let uu____3799 =
                          let uu____3802 =
                            let uu____3803 =
                              let uu____3810 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3810)  in
                            FStar_Syntax_Syntax.NT uu____3803  in
                          [uu____3802]  in
                        FStar_Syntax_Subst.subst uu____3799 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3797
                        uu____3798 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3794
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3818  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3688
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3837 = cur_goal ()  in
      bind uu____3837
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3845 = FStar_Tactics_Types.goal_env goal  in
               let uu____3846 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3845 uu____3846
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3848 = __tc env t  in
           bind uu____3848
             (fun uu____3867  ->
                match uu____3867 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3882  ->
                         let uu____3883 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3884 =
                           let uu____3885 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3885
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3883 uu____3884)
                      (fun uu____3888  ->
                         let uu____3889 =
                           let uu____3892 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3892 guard  in
                         bind uu____3889
                           (fun uu____3894  ->
                              mlog
                                (fun uu____3898  ->
                                   let uu____3899 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3900 =
                                     let uu____3901 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3901
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3899 uu____3900)
                                (fun uu____3904  ->
                                   let uu____3905 =
                                     let uu____3908 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3909 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3908 typ uu____3909  in
                                   bind uu____3905
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3915 =
                                             let uu____3916 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3916 t1  in
                                           let uu____3917 =
                                             let uu____3918 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3918 typ  in
                                           let uu____3919 =
                                             let uu____3920 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3921 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3920 uu____3921  in
                                           let uu____3922 =
                                             let uu____3923 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3924 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3923 uu____3924  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3915 uu____3917 uu____3919
                                             uu____3922)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3944 =
          mlog
            (fun uu____3949  ->
               let uu____3950 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3950)
            (fun uu____3953  ->
               let uu____3954 =
                 let uu____3961 = __exact_now set_expected_typ1 tm  in
                 catch uu____3961  in
               bind uu____3954
                 (fun uu___349_3970  ->
                    match uu___349_3970 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3981  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3984  ->
                             let uu____3985 =
                               let uu____3992 =
                                 let uu____3995 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3995
                                   (fun uu____4000  ->
                                      let uu____4001 = refine_intro ()  in
                                      bind uu____4001
                                        (fun uu____4005  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3992  in
                             bind uu____3985
                               (fun uu___348_4012  ->
                                  match uu___348_4012 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4021  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4023  -> ret ())
                                  | FStar_Util.Inl uu____4024 ->
                                      mlog
                                        (fun uu____4026  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4028  -> fail e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3944
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4078 = f x  in
          bind uu____4078
            (fun y  ->
               let uu____4086 = mapM f xs  in
               bind uu____4086 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4157 = do_unify e ty1 ty2  in
          bind uu____4157
            (fun uu___350_4169  ->
               if uu___350_4169
               then ret acc
               else
                 (let uu____4188 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4188 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4209 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4210 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4209
                        uu____4210
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4225 =
                        let uu____4226 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4226  in
                      if uu____4225
                      then fail "Codomain is effectful"
                      else
                        (let uu____4246 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4246
                           (fun uu____4272  ->
                              match uu____4272 with
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
      let uu____4358 =
        mlog
          (fun uu____4363  ->
             let uu____4364 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4364)
          (fun uu____4367  ->
             let uu____4368 = cur_goal ()  in
             bind uu____4368
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4376 = __tc e tm  in
                  bind uu____4376
                    (fun uu____4397  ->
                       match uu____4397 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4410 =
                             let uu____4421 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4421  in
                           bind uu____4410
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4464  ->
                                       fun w  ->
                                         match uu____4464 with
                                         | (uvt,q,uu____4482) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4514 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4531  ->
                                       fun s  ->
                                         match uu____4531 with
                                         | (uu____4543,uu____4544,uv) ->
                                             let uu____4546 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4546) uvs uu____4514
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4555 = solve' goal w  in
                                bind uu____4555
                                  (fun uu____4560  ->
                                     let uu____4561 =
                                       mapM
                                         (fun uu____4578  ->
                                            match uu____4578 with
                                            | (uvt,q,uv) ->
                                                let uu____4590 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4590 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4595 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4596 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4596
                                                     then ret ()
                                                     else
                                                       (let uu____4600 =
                                                          let uu____4603 =
                                                            bnorm_goal
                                                              (let uu___396_4606
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___396_4606.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___396_4606.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4603]  in
                                                        add_goals uu____4600)))
                                         uvs
                                        in
                                     bind uu____4561
                                       (fun uu____4610  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4358
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4635 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4635
    then
      let uu____4642 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4657 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4710 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4642 with
      | (pre,post) ->
          let post1 =
            let uu____4742 =
              let uu____4753 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4753]  in
            FStar_Syntax_Util.mk_app post uu____4742  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4783 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4783
       then
         let uu____4790 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4790
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4823 =
      let uu____4826 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4833  ->
                  let uu____4834 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4834)
               (fun uu____4838  ->
                  let is_unit_t t =
                    let uu____4845 =
                      let uu____4846 = FStar_Syntax_Subst.compress t  in
                      uu____4846.FStar_Syntax_Syntax.n  in
                    match uu____4845 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4850 -> false  in
                  let uu____4851 = cur_goal ()  in
                  bind uu____4851
                    (fun goal  ->
                       let uu____4857 =
                         let uu____4866 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4866 tm  in
                       bind uu____4857
                         (fun uu____4881  ->
                            match uu____4881 with
                            | (tm1,t,guard) ->
                                let uu____4893 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4893 with
                                 | (bs,comp) ->
                                     let uu____4926 = lemma_or_sq comp  in
                                     (match uu____4926 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4945 =
                                            FStar_List.fold_left
                                              (fun uu____4993  ->
                                                 fun uu____4994  ->
                                                   match (uu____4993,
                                                           uu____4994)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5107 =
                                                         is_unit_t b_t  in
                                                       if uu____5107
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5145 =
                                                            let uu____5158 =
                                                              let uu____5159
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5159.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5162 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5158
                                                              uu____5162 b_t
                                                             in
                                                          match uu____5145
                                                          with
                                                          | (u,uu____5180,g_u)
                                                              ->
                                                              let uu____5194
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5194,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4945 with
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
                                               let uu____5273 =
                                                 let uu____5276 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5277 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5278 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5276
                                                   uu____5277 uu____5278
                                                  in
                                               bind uu____5273
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5286 =
                                                        let uu____5287 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5287 tm1
                                                         in
                                                      let uu____5288 =
                                                        let uu____5289 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5290 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5289
                                                          uu____5290
                                                         in
                                                      let uu____5291 =
                                                        let uu____5292 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5293 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5292
                                                          uu____5293
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5286 uu____5288
                                                        uu____5291
                                                    else
                                                      (let uu____5295 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5295
                                                         (fun uu____5300  ->
                                                            let uu____5301 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5301
                                                              (fun uu____5309
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5334
                                                                    =
                                                                    let uu____5337
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5337
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5334
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
                                                                    let uu____5372
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5372)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5388
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5388
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5406)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5432)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5449
                                                                    -> false)
                                                                    in
                                                                 let uu____5450
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
                                                                    let uu____5480
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5480
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5502)
                                                                    ->
                                                                    let uu____5527
                                                                    =
                                                                    let uu____5528
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5528.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5527
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5536)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___397_5556
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___397_5556.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___397_5556.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___397_5556.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5559
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5565
                                                                     ->
                                                                    let uu____5566
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5567
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5566
                                                                    uu____5567)
                                                                    (fun
                                                                    uu____5572
                                                                     ->
                                                                    let env =
                                                                    let uu___398_5574
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___398_5574.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5576
                                                                    =
                                                                    let uu____5579
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5580
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5581
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5580
                                                                    uu____5581
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5583
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5579
                                                                    uu____5583
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5576
                                                                    (fun
                                                                    uu____5587
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5450
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
                                                                    let uu____5649
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5649
                                                                    then
                                                                    let uu____5652
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5652
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
                                                                    let uu____5666
                                                                    =
                                                                    let uu____5667
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5667
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5666)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5668
                                                                    =
                                                                    let uu____5671
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5671
                                                                    guard  in
                                                                    bind
                                                                    uu____5668
                                                                    (fun
                                                                    uu____5674
                                                                     ->
                                                                    let uu____5675
                                                                    =
                                                                    let uu____5678
                                                                    =
                                                                    let uu____5679
                                                                    =
                                                                    let uu____5680
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5681
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5680
                                                                    uu____5681
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5679
                                                                     in
                                                                    if
                                                                    uu____5678
                                                                    then
                                                                    let uu____5684
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5684
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5675
                                                                    (fun
                                                                    uu____5687
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4826  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4823
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5709 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5709 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5719::(e1,uu____5721)::(e2,uu____5723)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5784 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5808 = destruct_eq' typ  in
    match uu____5808 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5838 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5838 with
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
        let uu____5900 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5900 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5948 = aux e'  in
               FStar_Util.map_opt uu____5948
                 (fun uu____5972  ->
                    match uu____5972 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5993 = aux e  in
      FStar_Util.map_opt uu____5993
        (fun uu____6017  ->
           match uu____6017 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____6084 =
            let uu____6093 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6093  in
          FStar_Util.map_opt uu____6084
            (fun uu____6108  ->
               match uu____6108 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___399_6127 = bv  in
                     let uu____6128 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___399_6127.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___399_6127.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6128
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___400_6136 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6137 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6146 =
                       let uu____6149 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6149  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___400_6136.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6137;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6146;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___400_6136.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___400_6136.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___400_6136.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___401_6150 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___401_6150.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___401_6150.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___401_6150.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6160 =
      let uu____6163 = cur_goal ()  in
      bind uu____6163
        (fun goal  ->
           let uu____6171 = h  in
           match uu____6171 with
           | (bv,uu____6175) ->
               mlog
                 (fun uu____6183  ->
                    let uu____6184 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6185 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6184
                      uu____6185)
                 (fun uu____6188  ->
                    let uu____6189 =
                      let uu____6198 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6198  in
                    match uu____6189 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6219 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6219 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6234 =
                               let uu____6235 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6235.FStar_Syntax_Syntax.n  in
                             (match uu____6234 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___402_6252 = bv1  in
                                    let uu____6253 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___402_6252.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___402_6252.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6253
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___403_6261 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6262 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6271 =
                                      let uu____6274 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6274
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___403_6261.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6262;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6271;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___403_6261.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___403_6261.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___403_6261.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___404_6277 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___404_6277.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___404_6277.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___404_6277.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6278 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6279 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6160
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6304 =
        let uu____6307 = cur_goal ()  in
        bind uu____6307
          (fun goal  ->
             let uu____6318 = b  in
             match uu____6318 with
             | (bv,uu____6322) ->
                 let bv' =
                   let uu____6328 =
                     let uu___405_6329 = bv  in
                     let uu____6330 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6330;
                       FStar_Syntax_Syntax.index =
                         (uu___405_6329.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___405_6329.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6328  in
                 let s1 =
                   let uu____6334 =
                     let uu____6335 =
                       let uu____6342 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6342)  in
                     FStar_Syntax_Syntax.NT uu____6335  in
                   [uu____6334]  in
                 let uu____6347 = subst_goal bv bv' s1 goal  in
                 (match uu____6347 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6304
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6366 =
      let uu____6369 = cur_goal ()  in
      bind uu____6369
        (fun goal  ->
           let uu____6378 = b  in
           match uu____6378 with
           | (bv,uu____6382) ->
               let uu____6387 =
                 let uu____6396 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6396  in
               (match uu____6387 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6417 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6417 with
                     | (ty,u) ->
                         let uu____6426 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6426
                           (fun uu____6444  ->
                              match uu____6444 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___406_6454 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___406_6454.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___406_6454.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6458 =
                                      let uu____6459 =
                                        let uu____6466 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6466)  in
                                      FStar_Syntax_Syntax.NT uu____6459  in
                                    [uu____6458]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___407_6478 = b1  in
                                         let uu____6479 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___407_6478.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___407_6478.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6479
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6486  ->
                                       let new_goal =
                                         let uu____6488 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6489 =
                                           let uu____6490 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6490
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6488 uu____6489
                                          in
                                       let uu____6491 = add_goals [new_goal]
                                          in
                                       bind uu____6491
                                         (fun uu____6496  ->
                                            let uu____6497 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6497
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6366
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6520 =
        let uu____6523 = cur_goal ()  in
        bind uu____6523
          (fun goal  ->
             let uu____6532 = b  in
             match uu____6532 with
             | (bv,uu____6536) ->
                 let uu____6541 =
                   let uu____6550 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6550  in
                 (match uu____6541 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6574 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6574
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___408_6579 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___408_6579.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___408_6579.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6581 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6581))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6520
  
let (revert : unit -> unit tac) =
  fun uu____6592  ->
    let uu____6595 = cur_goal ()  in
    bind uu____6595
      (fun goal  ->
         let uu____6601 =
           let uu____6608 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6608  in
         match uu____6601 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6624 =
                 let uu____6627 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6627  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6624
                in
             let uu____6642 = new_uvar "revert" env' typ'  in
             bind uu____6642
               (fun uu____6657  ->
                  match uu____6657 with
                  | (r,u_r) ->
                      let uu____6666 =
                        let uu____6669 =
                          let uu____6670 =
                            let uu____6671 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6671.FStar_Syntax_Syntax.pos  in
                          let uu____6674 =
                            let uu____6679 =
                              let uu____6680 =
                                let uu____6689 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6689  in
                              [uu____6680]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6679  in
                          uu____6674 FStar_Pervasives_Native.None uu____6670
                           in
                        set_solution goal uu____6669  in
                      bind uu____6666
                        (fun uu____6710  ->
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
      let uu____6722 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6722
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6737 = cur_goal ()  in
    bind uu____6737
      (fun goal  ->
         mlog
           (fun uu____6745  ->
              let uu____6746 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6747 =
                let uu____6748 =
                  let uu____6749 =
                    let uu____6758 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6758  in
                  FStar_All.pipe_right uu____6749 FStar_List.length  in
                FStar_All.pipe_right uu____6748 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6746 uu____6747)
           (fun uu____6775  ->
              let uu____6776 =
                let uu____6785 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6785  in
              match uu____6776 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6824 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6824
                        then
                          let uu____6827 =
                            let uu____6828 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6828
                             in
                          fail uu____6827
                        else check1 bvs2
                     in
                  let uu____6830 =
                    let uu____6831 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6831  in
                  if uu____6830
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6835 = check1 bvs  in
                     bind uu____6835
                       (fun uu____6841  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6843 =
                            let uu____6850 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6850  in
                          bind uu____6843
                            (fun uu____6859  ->
                               match uu____6859 with
                               | (ut,uvar_ut) ->
                                   let uu____6868 = set_solution goal ut  in
                                   bind uu____6868
                                     (fun uu____6873  ->
                                        let uu____6874 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6874))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6881  ->
    let uu____6884 = cur_goal ()  in
    bind uu____6884
      (fun goal  ->
         let uu____6890 =
           let uu____6897 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6897  in
         match uu____6890 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6905) ->
             let uu____6910 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6910)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6920 = cur_goal ()  in
    bind uu____6920
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6930 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6930  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6933  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6943 = cur_goal ()  in
    bind uu____6943
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6953 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6953  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6956  -> add_goals [g']))
  
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
            let uu____6996 = FStar_Syntax_Subst.compress t  in
            uu____6996.FStar_Syntax_Syntax.n  in
          let uu____6999 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___412_7005 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___412_7005.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___412_7005.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6999
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7021 =
                   let uu____7022 = FStar_Syntax_Subst.compress t1  in
                   uu____7022.FStar_Syntax_Syntax.n  in
                 match uu____7021 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____7053 = ff hd1  in
                     bind uu____7053
                       (fun hd2  ->
                          let fa uu____7079 =
                            match uu____7079 with
                            | (a,q) ->
                                let uu____7100 = ff a  in
                                bind uu____7100 (fun a1  -> ret (a1, q))
                             in
                          let uu____7119 = mapM fa args  in
                          bind uu____7119
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7201 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7201 with
                      | (bs1,t') ->
                          let uu____7210 =
                            let uu____7213 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7213 t'  in
                          bind uu____7210
                            (fun t''  ->
                               let uu____7217 =
                                 let uu____7218 =
                                   let uu____7237 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7246 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7237, uu____7246, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7218  in
                               ret uu____7217))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7321 = ff hd1  in
                     bind uu____7321
                       (fun hd2  ->
                          let ffb br =
                            let uu____7336 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7336 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7368 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7368  in
                                let uu____7369 = ff1 e  in
                                bind uu____7369
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7384 = mapM ffb brs  in
                          bind uu____7384
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7428;
                          FStar_Syntax_Syntax.lbtyp = uu____7429;
                          FStar_Syntax_Syntax.lbeff = uu____7430;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7432;
                          FStar_Syntax_Syntax.lbpos = uu____7433;_}::[]),e)
                     ->
                     let lb =
                       let uu____7458 =
                         let uu____7459 = FStar_Syntax_Subst.compress t1  in
                         uu____7459.FStar_Syntax_Syntax.n  in
                       match uu____7458 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7463) -> lb
                       | uu____7476 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7485 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7485
                         (fun def1  ->
                            ret
                              (let uu___409_7491 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___409_7491.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___409_7491.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___409_7491.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___409_7491.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___409_7491.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___409_7491.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7492 = fflb lb  in
                     bind uu____7492
                       (fun lb1  ->
                          let uu____7502 =
                            let uu____7507 =
                              let uu____7508 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7508]  in
                            FStar_Syntax_Subst.open_term uu____7507 e  in
                          match uu____7502 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7538 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7538  in
                              let uu____7539 = ff1 e1  in
                              bind uu____7539
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7580 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7580
                         (fun def  ->
                            ret
                              (let uu___410_7586 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___410_7586.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___410_7586.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___410_7586.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___410_7586.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___410_7586.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___410_7586.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7587 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7587 with
                      | (lbs1,e1) ->
                          let uu____7602 = mapM fflb lbs1  in
                          bind uu____7602
                            (fun lbs2  ->
                               let uu____7614 = ff e1  in
                               bind uu____7614
                                 (fun e2  ->
                                    let uu____7622 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7622 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7690 = ff t2  in
                     bind uu____7690
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7721 = ff t2  in
                     bind uu____7721
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7728 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___411_7735 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___411_7735.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___411_7735.FStar_Syntax_Syntax.vars)
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
            let uu____7772 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___413_7781 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___413_7781.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___413_7781.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___413_7781.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___413_7781.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___413_7781.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___413_7781.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___413_7781.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___413_7781.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___413_7781.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___413_7781.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___413_7781.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___413_7781.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___413_7781.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___413_7781.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___413_7781.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___413_7781.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___413_7781.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___413_7781.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___413_7781.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___413_7781.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___413_7781.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___413_7781.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___413_7781.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___413_7781.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___413_7781.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___413_7781.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___413_7781.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___413_7781.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___413_7781.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___413_7781.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___413_7781.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___413_7781.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___413_7781.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___413_7781.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___413_7781.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___413_7781.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___413_7781.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___413_7781.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___413_7781.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___413_7781.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___413_7781.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7772 with
            | (t1,lcomp,g) ->
                let uu____7787 =
                  (let uu____7790 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7790) ||
                    (let uu____7792 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7792)
                   in
                if uu____7787
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7800 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7800
                       (fun uu____7816  ->
                          match uu____7816 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7829  ->
                                    let uu____7830 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7831 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7830 uu____7831);
                               (let uu____7832 =
                                  let uu____7835 =
                                    let uu____7836 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7836 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7835
                                    opts
                                   in
                                bind uu____7832
                                  (fun uu____7839  ->
                                     let uu____7840 =
                                       bind tau
                                         (fun uu____7846  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7852  ->
                                                 let uu____7853 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7854 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7853 uu____7854);
                                            ret ut1)
                                        in
                                     focus uu____7840))))
                      in
                   let uu____7855 = catch rewrite_eq  in
                   bind uu____7855
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
          let uu____8053 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____8053
            (fun t1  ->
               let uu____8061 =
                 f env
                   (let uu___416_8070 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___416_8070.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___416_8070.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____8061
                 (fun uu____8086  ->
                    match uu____8086 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____8109 =
                               let uu____8110 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____8110.FStar_Syntax_Syntax.n  in
                             match uu____8109 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8147 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8147
                                   (fun uu____8172  ->
                                      match uu____8172 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8188 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8188
                                            (fun uu____8215  ->
                                               match uu____8215 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___414_8245 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___414_8245.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___414_8245.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8287 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8287 with
                                  | (bs1,t') ->
                                      let uu____8302 =
                                        let uu____8309 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8309 ctrl1 t'
                                         in
                                      bind uu____8302
                                        (fun uu____8327  ->
                                           match uu____8327 with
                                           | (t'',ctrl2) ->
                                               let uu____8342 =
                                                 let uu____8349 =
                                                   let uu___415_8352 = t4  in
                                                   let uu____8355 =
                                                     let uu____8356 =
                                                       let uu____8375 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8384 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8375,
                                                         uu____8384, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8356
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8355;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___415_8352.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___415_8352.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8349, ctrl2)  in
                                               ret uu____8342))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8437 -> ret (t3, ctrl1))))

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
              let uu____8484 = ctrl_tac_fold f env ctrl t  in
              bind uu____8484
                (fun uu____8508  ->
                   match uu____8508 with
                   | (t1,ctrl1) ->
                       let uu____8523 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8523
                         (fun uu____8550  ->
                            match uu____8550 with
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
              let uu____8634 =
                let uu____8641 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8641
                  (fun uu____8650  ->
                     let uu____8651 = ctrl t1  in
                     bind uu____8651
                       (fun res  ->
                          let uu____8674 = trivial ()  in
                          bind uu____8674 (fun uu____8682  -> ret res)))
                 in
              bind uu____8634
                (fun uu____8698  ->
                   match uu____8698 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8722 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___417_8731 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___417_8731.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___417_8731.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___417_8731.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___417_8731.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___417_8731.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___417_8731.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___417_8731.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___417_8731.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___417_8731.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___417_8731.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___417_8731.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___417_8731.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___417_8731.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___417_8731.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___417_8731.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___417_8731.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___417_8731.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___417_8731.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___417_8731.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___417_8731.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___417_8731.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___417_8731.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___417_8731.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___417_8731.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___417_8731.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___417_8731.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___417_8731.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___417_8731.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___417_8731.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___417_8731.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___417_8731.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___417_8731.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___417_8731.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___417_8731.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___417_8731.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___417_8731.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___417_8731.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___417_8731.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___417_8731.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___417_8731.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___417_8731.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8722 with
                          | (t2,lcomp,g) ->
                              let uu____8741 =
                                (let uu____8744 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8744) ||
                                  (let uu____8746 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8746)
                                 in
                              if uu____8741
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8759 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8759
                                   (fun uu____8779  ->
                                      match uu____8779 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8796  ->
                                                let uu____8797 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8798 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8797 uu____8798);
                                           (let uu____8799 =
                                              let uu____8802 =
                                                let uu____8803 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8803 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8802 opts
                                               in
                                            bind uu____8799
                                              (fun uu____8810  ->
                                                 let uu____8811 =
                                                   bind rewriter
                                                     (fun uu____8825  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8831  ->
                                                             let uu____8832 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8833 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8832
                                                               uu____8833);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8811)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8874 =
        bind get
          (fun ps  ->
             let uu____8884 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8884 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8921  ->
                       let uu____8922 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8922);
                  bind dismiss_all
                    (fun uu____8925  ->
                       let uu____8926 =
                         let uu____8933 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8933
                           keepGoing gt1
                          in
                       bind uu____8926
                         (fun uu____8945  ->
                            match uu____8945 with
                            | (gt',uu____8953) ->
                                (log ps
                                   (fun uu____8957  ->
                                      let uu____8958 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8958);
                                 (let uu____8959 = push_goals gs  in
                                  bind uu____8959
                                    (fun uu____8964  ->
                                       let uu____8965 =
                                         let uu____8968 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8968]  in
                                       add_goals uu____8965)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8874
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8991 =
        bind get
          (fun ps  ->
             let uu____9001 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9001 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9038  ->
                       let uu____9039 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____9039);
                  bind dismiss_all
                    (fun uu____9042  ->
                       let uu____9043 =
                         let uu____9046 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____9046 gt1
                          in
                       bind uu____9043
                         (fun gt'  ->
                            log ps
                              (fun uu____9054  ->
                                 let uu____9055 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____9055);
                            (let uu____9056 = push_goals gs  in
                             bind uu____9056
                               (fun uu____9061  ->
                                  let uu____9062 =
                                    let uu____9065 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____9065]  in
                                  add_goals uu____9062))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8991
  
let (trefl : unit -> unit tac) =
  fun uu____9076  ->
    let uu____9079 =
      let uu____9082 = cur_goal ()  in
      bind uu____9082
        (fun g  ->
           let uu____9100 =
             let uu____9105 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____9105  in
           match uu____9100 with
           | FStar_Pervasives_Native.Some t ->
               let uu____9113 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____9113 with
                | (hd1,args) ->
                    let uu____9152 =
                      let uu____9165 =
                        let uu____9166 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9166.FStar_Syntax_Syntax.n  in
                      (uu____9165, args)  in
                    (match uu____9152 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9180::(l,uu____9182)::(r,uu____9184)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9231 =
                           let uu____9234 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9234 l r  in
                         bind uu____9231
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9241 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9241 l
                                    in
                                 let r1 =
                                   let uu____9243 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9243 r
                                    in
                                 let uu____9244 =
                                   let uu____9247 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9247 l1 r1  in
                                 bind uu____9244
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9253 =
                                           let uu____9254 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9254 l1  in
                                         let uu____9255 =
                                           let uu____9256 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9256 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9253 uu____9255))))
                     | (hd2,uu____9258) ->
                         let uu____9275 =
                           let uu____9276 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9276 t  in
                         fail1 "trefl: not an equality (%s)" uu____9275))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____9079
  
let (dup : unit -> unit tac) =
  fun uu____9289  ->
    let uu____9292 = cur_goal ()  in
    bind uu____9292
      (fun g  ->
         let uu____9298 =
           let uu____9305 = FStar_Tactics_Types.goal_env g  in
           let uu____9306 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9305 uu____9306  in
         bind uu____9298
           (fun uu____9315  ->
              match uu____9315 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___418_9325 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___418_9325.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___418_9325.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___418_9325.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9328  ->
                       let uu____9329 =
                         let uu____9332 = FStar_Tactics_Types.goal_env g  in
                         let uu____9333 =
                           let uu____9334 =
                             let uu____9335 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9336 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9335
                               uu____9336
                              in
                           let uu____9337 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9338 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9334 uu____9337 u
                             uu____9338
                            in
                         add_irrelevant_goal "dup equation" uu____9332
                           uu____9333 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9329
                         (fun uu____9341  ->
                            let uu____9342 = add_goals [g']  in
                            bind uu____9342 (fun uu____9346  -> ret ())))))
  
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
              let uu____9469 = f x y  in
              if uu____9469 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9489 -> (acc, l11, l21)  in
        let uu____9504 = aux [] l1 l2  in
        match uu____9504 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9609 = get_phi g1  in
      match uu____9609 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9615 = get_phi g2  in
          (match uu____9615 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9627 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9627 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9658 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____9658 phi1  in
                    let t2 =
                      let uu____9668 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____9668 phi2  in
                    let uu____9677 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9677
                      (fun uu____9682  ->
                         let uu____9683 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9683
                           (fun uu____9690  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___419_9695 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9696 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___419_9695.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___419_9695.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___419_9695.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___419_9695.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9696;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___419_9695.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___419_9695.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___419_9695.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___419_9695.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___419_9695.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___419_9695.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___419_9695.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___419_9695.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___419_9695.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___419_9695.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___419_9695.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___419_9695.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___419_9695.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___419_9695.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___419_9695.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___419_9695.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___419_9695.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___419_9695.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___419_9695.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___419_9695.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___419_9695.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___419_9695.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___419_9695.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___419_9695.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___419_9695.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___419_9695.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___419_9695.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___419_9695.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___419_9695.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___419_9695.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___419_9695.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___419_9695.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___419_9695.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___419_9695.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___419_9695.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___419_9695.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9699 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9699
                                (fun goal  ->
                                   mlog
                                     (fun uu____9708  ->
                                        let uu____9709 =
                                          goal_to_string_verbose g1  in
                                        let uu____9710 =
                                          goal_to_string_verbose g2  in
                                        let uu____9711 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9709 uu____9710 uu____9711)
                                     (fun uu____9713  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9720  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9736 =
               set
                 (let uu___420_9741 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___420_9741.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___420_9741.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___420_9741.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___420_9741.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___420_9741.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___420_9741.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___420_9741.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___420_9741.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___420_9741.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___420_9741.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___420_9741.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___420_9741.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9736
               (fun uu____9744  ->
                  let uu____9745 = join_goals g1 g2  in
                  bind uu____9745 (fun g12  -> add_goals [g12]))
         | uu____9750 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9770 =
      let uu____9777 = cur_goal ()  in
      bind uu____9777
        (fun g  ->
           let uu____9787 =
             let uu____9796 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9796 t  in
           bind uu____9787
             (fun uu____9824  ->
                match uu____9824 with
                | (t1,typ,guard) ->
                    let uu____9840 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9840 with
                     | (hd1,args) ->
                         let uu____9889 =
                           let uu____9904 =
                             let uu____9905 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9905.FStar_Syntax_Syntax.n  in
                           (uu____9904, args)  in
                         (match uu____9889 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9926)::(q,uu____9928)::[]) when
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
                                let uu____9982 =
                                  let uu____9983 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9983
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9982
                                 in
                              let g2 =
                                let uu____9985 =
                                  let uu____9986 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9986
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9985
                                 in
                              bind __dismiss
                                (fun uu____9993  ->
                                   let uu____9994 = add_goals [g1; g2]  in
                                   bind uu____9994
                                     (fun uu____10003  ->
                                        let uu____10004 =
                                          let uu____10009 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____10010 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____10009, uu____10010)  in
                                        ret uu____10004))
                          | uu____10015 ->
                              let uu____10030 =
                                let uu____10031 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____10031 typ  in
                              fail1 "Not a disjunction: %s" uu____10030))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9770
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____10061 =
      let uu____10064 = cur_goal ()  in
      bind uu____10064
        (fun g  ->
           FStar_Options.push ();
           (let uu____10077 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____10077);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___421_10084 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___421_10084.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___421_10084.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___421_10084.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____10061
  
let (top_env : unit -> env tac) =
  fun uu____10096  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10109  ->
    let uu____10112 = cur_goal ()  in
    bind uu____10112
      (fun g  ->
         let uu____10118 =
           (FStar_Options.lax ()) ||
             (let uu____10120 = FStar_Tactics_Types.goal_env g  in
              uu____10120.FStar_TypeChecker_Env.lax)
            in
         ret uu____10118)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10135 =
        mlog
          (fun uu____10140  ->
             let uu____10141 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10141)
          (fun uu____10144  ->
             let uu____10145 = cur_goal ()  in
             bind uu____10145
               (fun goal  ->
                  let env =
                    let uu____10153 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10153 ty  in
                  let uu____10154 = __tc_ghost env tm  in
                  bind uu____10154
                    (fun uu____10173  ->
                       match uu____10173 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10187  ->
                                let uu____10188 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10188)
                             (fun uu____10190  ->
                                mlog
                                  (fun uu____10193  ->
                                     let uu____10194 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10194)
                                  (fun uu____10197  ->
                                     let uu____10198 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10198
                                       (fun uu____10202  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10135
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10225 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10231 =
              let uu____10238 =
                let uu____10239 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10239
                 in
              new_uvar "uvar_env.2" env uu____10238  in
            bind uu____10231
              (fun uu____10255  ->
                 match uu____10255 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10225
        (fun typ  ->
           let uu____10267 = new_uvar "uvar_env" env typ  in
           bind uu____10267
             (fun uu____10281  ->
                match uu____10281 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10299 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10318 -> g.FStar_Tactics_Types.opts
             | uu____10321 -> FStar_Options.peek ()  in
           let uu____10324 = FStar_Syntax_Util.head_and_args t  in
           match uu____10324 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10344);
                FStar_Syntax_Syntax.pos = uu____10345;
                FStar_Syntax_Syntax.vars = uu____10346;_},uu____10347)
               ->
               let env1 =
                 let uu___422_10389 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___422_10389.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___422_10389.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___422_10389.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___422_10389.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___422_10389.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___422_10389.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___422_10389.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___422_10389.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___422_10389.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___422_10389.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___422_10389.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___422_10389.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___422_10389.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___422_10389.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___422_10389.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___422_10389.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___422_10389.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___422_10389.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___422_10389.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___422_10389.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___422_10389.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___422_10389.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___422_10389.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___422_10389.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___422_10389.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___422_10389.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___422_10389.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___422_10389.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___422_10389.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___422_10389.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___422_10389.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___422_10389.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___422_10389.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___422_10389.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___422_10389.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___422_10389.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___422_10389.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___422_10389.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___422_10389.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___422_10389.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___422_10389.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10391 =
                 let uu____10394 = bnorm_goal g  in [uu____10394]  in
               add_goals uu____10391
           | uu____10395 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10299
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10444 = if b then t2 else ret false  in
             bind uu____10444 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10455 = trytac comp  in
      bind uu____10455
        (fun uu___351_10463  ->
           match uu___351_10463 with
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
        let uu____10489 =
          bind get
            (fun ps  ->
               let uu____10495 = __tc e t1  in
               bind uu____10495
                 (fun uu____10515  ->
                    match uu____10515 with
                    | (t11,ty1,g1) ->
                        let uu____10527 = __tc e t2  in
                        bind uu____10527
                          (fun uu____10547  ->
                             match uu____10547 with
                             | (t21,ty2,g2) ->
                                 let uu____10559 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10559
                                   (fun uu____10564  ->
                                      let uu____10565 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10565
                                        (fun uu____10571  ->
                                           let uu____10572 =
                                             do_unify e ty1 ty2  in
                                           let uu____10575 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10572 uu____10575)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10489
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10608  ->
             let uu____10609 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10609
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
        (fun uu____10630  ->
           let uu____10631 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10631)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10641 =
      mlog
        (fun uu____10646  ->
           let uu____10647 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10647)
        (fun uu____10650  ->
           let uu____10651 = cur_goal ()  in
           bind uu____10651
             (fun g  ->
                let uu____10657 =
                  let uu____10666 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10666 ty  in
                bind uu____10657
                  (fun uu____10678  ->
                     match uu____10678 with
                     | (ty1,uu____10688,guard) ->
                         let uu____10690 =
                           let uu____10693 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10693 guard  in
                         bind uu____10690
                           (fun uu____10696  ->
                              let uu____10697 =
                                let uu____10700 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10701 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10700 uu____10701 ty1  in
                              bind uu____10697
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10707 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10707
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10713 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10714 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10713
                                          uu____10714
                                         in
                                      let nty =
                                        let uu____10716 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10716 ty1  in
                                      let uu____10717 =
                                        let uu____10720 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10720 ng nty  in
                                      bind uu____10717
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10726 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10726
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10641
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10789 =
      let uu____10798 = cur_goal ()  in
      bind uu____10798
        (fun g  ->
           let uu____10810 =
             let uu____10819 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10819 s_tm  in
           bind uu____10810
             (fun uu____10837  ->
                match uu____10837 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10855 =
                      let uu____10858 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10858 guard  in
                    bind uu____10855
                      (fun uu____10870  ->
                         let uu____10871 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10871 with
                         | (h,args) ->
                             let uu____10916 =
                               let uu____10923 =
                                 let uu____10924 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10924.FStar_Syntax_Syntax.n  in
                               match uu____10923 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10939;
                                      FStar_Syntax_Syntax.vars = uu____10940;_},us)
                                   -> ret (fv, us)
                               | uu____10950 -> fail "type is not an fv"  in
                             bind uu____10916
                               (fun uu____10970  ->
                                  match uu____10970 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10986 =
                                        let uu____10989 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10989 t_lid
                                         in
                                      (match uu____10986 with
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
                                                  (fun uu____11038  ->
                                                     let uu____11039 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____11039 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____11054 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____11082
                                                                  =
                                                                  let uu____11085
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____11085
                                                                    c_lid
                                                                   in
                                                                match uu____11082
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
                                                                    uu____11155
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
                                                                    let uu____11160
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11160
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11183
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11183
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11226
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11226
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11299
                                                                    =
                                                                    let uu____11300
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11300
                                                                     in
                                                                    failwhen
                                                                    uu____11299
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11317
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
                                                                    uu___352_11333
                                                                    =
                                                                    match uu___352_11333
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11336)
                                                                    -> true
                                                                    | 
                                                                    uu____11337
                                                                    -> false
                                                                     in
                                                                    let uu____11340
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11340
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
                                                                    uu____11473
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
                                                                    uu____11535
                                                                     ->
                                                                    match uu____11535
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11555),
                                                                    (t,uu____11557))
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
                                                                    uu____11625
                                                                     ->
                                                                    match uu____11625
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11651),
                                                                    (t,uu____11653))
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
                                                                    uu____11708
                                                                     ->
                                                                    match uu____11708
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
                                                                    let uu____11758
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___423_11775
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___423_11775.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____11758
                                                                    with
                                                                    | 
                                                                    (uu____11788,uu____11789,uu____11790,pat_t,uu____11792,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11799
                                                                    =
                                                                    let uu____11800
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11800
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11799
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11804
                                                                    =
                                                                    let uu____11813
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11813]
                                                                     in
                                                                    let uu____11832
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11804
                                                                    uu____11832
                                                                     in
                                                                    let nty =
                                                                    let uu____11838
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11838
                                                                     in
                                                                    let uu____11841
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11841
                                                                    (fun
                                                                    uu____11870
                                                                     ->
                                                                    match uu____11870
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
                                                                    let uu____11896
                                                                    =
                                                                    let uu____11907
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11907]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11896
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11943
                                                                    =
                                                                    let uu____11954
                                                                    =
                                                                    let uu____11959
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11959)
                                                                     in
                                                                    (g', br,
                                                                    uu____11954)
                                                                     in
                                                                    ret
                                                                    uu____11943))))))
                                                                    | 
                                                                    uu____11980
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____11054
                                                           (fun goal_brs  ->
                                                              let uu____12029
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____12029
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
                                                                  let uu____12102
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12102
                                                                    (
                                                                    fun
                                                                    uu____12113
                                                                     ->
                                                                    let uu____12114
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12114
                                                                    (fun
                                                                    uu____12124
                                                                     ->
                                                                    ret infos))))
                                            | uu____12131 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10789
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12176::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12204 = init xs  in x :: uu____12204
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12216 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12225) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12290 = last args  in
          (match uu____12290 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12320 =
                 let uu____12321 =
                   let uu____12326 =
                     let uu____12327 =
                       let uu____12332 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12332  in
                     uu____12327 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12326, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12321  in
               FStar_All.pipe_left ret uu____12320)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12345,uu____12346) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12398 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12398 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12439 =
                      let uu____12440 =
                        let uu____12445 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12445)  in
                      FStar_Reflection_Data.Tv_Abs uu____12440  in
                    FStar_All.pipe_left ret uu____12439))
      | FStar_Syntax_Syntax.Tm_type uu____12448 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12472 ->
          let uu____12487 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12487 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12517 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12517 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12570 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12582 =
            let uu____12583 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12583  in
          FStar_All.pipe_left ret uu____12582
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12604 =
            let uu____12605 =
              let uu____12610 =
                let uu____12611 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12611  in
              (uu____12610, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12605  in
          FStar_All.pipe_left ret uu____12604
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12645 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12650 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12650 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12703 ->
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
             | FStar_Util.Inr uu____12737 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12741 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12741 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12761 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12765 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12819 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12819
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12838 =
                  let uu____12845 =
                    FStar_List.map
                      (fun uu____12857  ->
                         match uu____12857 with
                         | (p1,uu____12865) -> inspect_pat p1) ps
                     in
                  (fv, uu____12845)  in
                FStar_Reflection_Data.Pat_Cons uu____12838
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
              (fun uu___353_12959  ->
                 match uu___353_12959 with
                 | (pat,uu____12981,t5) ->
                     let uu____12999 = inspect_pat pat  in (uu____12999, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____13008 ->
          ((let uu____13010 =
              let uu____13015 =
                let uu____13016 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____13017 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____13016 uu____13017
                 in
              (FStar_Errors.Warning_CantInspect, uu____13015)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____13010);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12216
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____13030 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____13030
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____13034 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____13034
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____13038 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____13038
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____13045 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____13045
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____13070 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____13070
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____13087 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____13087
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13106 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13106
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13110 =
          let uu____13111 =
            let uu____13118 =
              let uu____13119 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13119  in
            FStar_Syntax_Syntax.mk uu____13118  in
          uu____13111 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13110
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13127 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13127
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13136 =
          let uu____13137 =
            let uu____13144 =
              let uu____13145 =
                let uu____13158 =
                  let uu____13161 =
                    let uu____13162 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13162]  in
                  FStar_Syntax_Subst.close uu____13161 t2  in
                ((false, [lb]), uu____13158)  in
              FStar_Syntax_Syntax.Tm_let uu____13145  in
            FStar_Syntax_Syntax.mk uu____13144  in
          uu____13137 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13136
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13202 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13202 with
         | (lbs,body) ->
             let uu____13217 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13217)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13251 =
                let uu____13252 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13252  in
              FStar_All.pipe_left wrap uu____13251
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13259 =
                let uu____13260 =
                  let uu____13273 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13289 = pack_pat p1  in
                         (uu____13289, false)) ps
                     in
                  (fv, uu____13273)  in
                FStar_Syntax_Syntax.Pat_cons uu____13260  in
              FStar_All.pipe_left wrap uu____13259
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
            (fun uu___354_13335  ->
               match uu___354_13335 with
               | (pat,t1) ->
                   let uu____13352 = pack_pat pat  in
                   (uu____13352, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13400 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13400
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13428 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13428
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13474 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13474
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13513 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13513
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13530 =
        bind get
          (fun ps  ->
             let uu____13536 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13536 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13530
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13565 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___424_13572 = ps  in
                 let uu____13573 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___424_13572.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___424_13572.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___424_13572.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___424_13572.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___424_13572.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___424_13572.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___424_13572.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___424_13572.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___424_13572.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___424_13572.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___424_13572.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___424_13572.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13573
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13565
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13598 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13598 with
      | (u,ctx_uvars,g_u) ->
          let uu____13630 = FStar_List.hd ctx_uvars  in
          (match uu____13630 with
           | (ctx_uvar,uu____13644) ->
               let g =
                 let uu____13646 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13646 false
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
        let uu____13666 = goal_of_goal_ty env typ  in
        match uu____13666 with
        | (g,g_u) ->
            let ps =
              let uu____13678 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13679 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13678;
                FStar_Tactics_Types.local_state = uu____13679
              }  in
            let uu____13686 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13686)
  