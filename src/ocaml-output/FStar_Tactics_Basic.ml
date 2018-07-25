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
  
let (tadmit : unit -> unit tac) =
  fun uu____1911  ->
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
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1914
  
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
  fun uu____2289  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___380_2307 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___380_2307.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___380_2307.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___380_2307.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___380_2307.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___380_2307.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___380_2307.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___380_2307.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___380_2307.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___380_2307.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___380_2307.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___380_2307.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___380_2307.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2331 = get_guard_policy ()  in
      bind uu____2331
        (fun old_pol  ->
           let uu____2337 = set_guard_policy pol  in
           bind uu____2337
             (fun uu____2341  ->
                bind t
                  (fun r  ->
                     let uu____2345 = set_guard_policy old_pol  in
                     bind uu____2345 (fun uu____2349  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2352 = let uu____2357 = cur_goal ()  in trytac uu____2357  in
  bind uu____2352
    (fun uu___347_2364  ->
       match uu___347_2364 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2370 = FStar_Options.peek ()  in ret uu____2370)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2392  ->
             let uu____2393 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2393)
          (fun uu____2396  ->
             let uu____2397 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2397
               (fun uu____2401  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2405 =
                         let uu____2406 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2406.FStar_TypeChecker_Env.guard_f  in
                       match uu____2405 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2410 = istrivial e f  in
                           if uu____2410
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2420 =
                                          let uu____2425 =
                                            let uu____2426 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2426
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2425)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2420);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2429  ->
                                           let uu____2430 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2430)
                                        (fun uu____2433  ->
                                           let uu____2434 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2434
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___381_2441 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___381_2441.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___381_2441.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___381_2441.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2444  ->
                                           let uu____2445 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2445)
                                        (fun uu____2448  ->
                                           let uu____2449 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2449
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___382_2456 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___382_2456.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___382_2456.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___382_2456.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2459  ->
                                           let uu____2460 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2460)
                                        (fun uu____2462  ->
                                           try
                                             (fun uu___384_2467  ->
                                                match () with
                                                | () ->
                                                    let uu____2470 =
                                                      let uu____2471 =
                                                        let uu____2472 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2472
                                                         in
                                                      Prims.op_Negation
                                                        uu____2471
                                                       in
                                                    if uu____2470
                                                    then
                                                      mlog
                                                        (fun uu____2477  ->
                                                           let uu____2478 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2478)
                                                        (fun uu____2480  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___383_2483 ->
                                               mlog
                                                 (fun uu____2488  ->
                                                    let uu____2489 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2489)
                                                 (fun uu____2491  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2501 =
      let uu____2504 = cur_goal ()  in
      bind uu____2504
        (fun goal  ->
           let uu____2510 =
             let uu____2519 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2519 t  in
           bind uu____2510
             (fun uu____2530  ->
                match uu____2530 with
                | (uu____2539,typ,uu____2541) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2501
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2570 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2570 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2581  ->
    let uu____2584 = cur_goal ()  in
    bind uu____2584
      (fun goal  ->
         let uu____2590 =
           let uu____2591 = FStar_Tactics_Types.goal_env goal  in
           let uu____2592 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2591 uu____2592  in
         if uu____2590
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2596 =
              let uu____2597 = FStar_Tactics_Types.goal_env goal  in
              let uu____2598 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2597 uu____2598  in
            fail1 "Not a trivial goal: %s" uu____2596))
  
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
          let uu____2627 =
            let uu____2628 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2628.FStar_TypeChecker_Env.guard_f  in
          match uu____2627 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2636 = istrivial e f  in
              if uu____2636
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2644 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2644
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___385_2654 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___385_2654.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___385_2654.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___385_2654.FStar_Tactics_Types.opts);
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
             let uu____2703 =
               try
                 (fun uu___390_2726  ->
                    match () with
                    | () ->
                        let uu____2737 =
                          let uu____2746 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2746
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2737) ()
               with | uu___389_2756 -> fail "divide: not enough goals"  in
             bind uu____2703
               (fun uu____2792  ->
                  match uu____2792 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___386_2818 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___386_2818.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___386_2818.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___386_2818.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___386_2818.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___386_2818.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___386_2818.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___386_2818.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___386_2818.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___386_2818.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___386_2818.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___386_2818.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2819 = set lp  in
                      bind uu____2819
                        (fun uu____2827  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___387_2843 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___387_2843.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___387_2843.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___387_2843.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___387_2843.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___387_2843.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___387_2843.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___387_2843.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___387_2843.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___387_2843.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___387_2843.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___387_2843.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2844 = set rp  in
                                     bind uu____2844
                                       (fun uu____2852  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___388_2868 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___388_2868.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___388_2868.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2869 = set p'
                                                       in
                                                    bind uu____2869
                                                      (fun uu____2877  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2883 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2904 = divide FStar_BigInt.one f idtac  in
    bind uu____2904
      (fun uu____2917  -> match uu____2917 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2954::uu____2955 ->
             let uu____2958 =
               let uu____2967 = map tau  in
               divide FStar_BigInt.one tau uu____2967  in
             bind uu____2958
               (fun uu____2985  ->
                  match uu____2985 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3026 =
        bind t1
          (fun uu____3031  ->
             let uu____3032 = map t2  in
             bind uu____3032 (fun uu____3040  -> ret ()))
         in
      focus uu____3026
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3049  ->
    let uu____3052 =
      let uu____3055 = cur_goal ()  in
      bind uu____3055
        (fun goal  ->
           let uu____3064 =
             let uu____3071 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3071  in
           match uu____3064 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3080 =
                 let uu____3081 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3081  in
               if uu____3080
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3086 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3086 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3100 = new_uvar "intro" env' typ'  in
                  bind uu____3100
                    (fun uu____3116  ->
                       match uu____3116 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3140 = set_solution goal sol  in
                           bind uu____3140
                             (fun uu____3146  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3148 =
                                  let uu____3151 = bnorm_goal g  in
                                  replace_cur uu____3151  in
                                bind uu____3148 (fun uu____3153  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3158 =
                 let uu____3159 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3160 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3159 uu____3160  in
               fail1 "goal is not an arrow (%s)" uu____3158)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3052
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3175  ->
    let uu____3182 = cur_goal ()  in
    bind uu____3182
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3199 =
            let uu____3206 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3206  in
          match uu____3199 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3219 =
                let uu____3220 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3220  in
              if uu____3219
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3233 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3233
                    in
                 let bs =
                   let uu____3243 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3243; b]  in
                 let env' =
                   let uu____3269 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3269 bs  in
                 let uu____3270 =
                   let uu____3277 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3277  in
                 bind uu____3270
                   (fun uu____3296  ->
                      match uu____3296 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3310 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3313 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3310
                              FStar_Parser_Const.effect_Tot_lid uu____3313 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3331 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3331 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3353 =
                                   let uu____3354 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3354.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3353
                                  in
                               let uu____3367 = set_solution goal tm  in
                               bind uu____3367
                                 (fun uu____3376  ->
                                    let uu____3377 =
                                      let uu____3380 =
                                        bnorm_goal
                                          (let uu___391_3383 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___391_3383.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___391_3383.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___391_3383.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3380  in
                                    bind uu____3377
                                      (fun uu____3390  ->
                                         let uu____3391 =
                                           let uu____3396 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3396, b)  in
                                         ret uu____3391)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3405 =
                let uu____3406 = FStar_Tactics_Types.goal_env goal  in
                let uu____3407 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3406 uu____3407  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3405))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3425 = cur_goal ()  in
    bind uu____3425
      (fun goal  ->
         mlog
           (fun uu____3432  ->
              let uu____3433 =
                let uu____3434 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3434  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3433)
           (fun uu____3439  ->
              let steps =
                let uu____3443 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3443
                 in
              let t =
                let uu____3447 = FStar_Tactics_Types.goal_env goal  in
                let uu____3448 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3447 uu____3448  in
              let uu____3449 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3449))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3473 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____3481 -> g.FStar_Tactics_Types.opts
                 | uu____3484 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____3489  ->
                    let uu____3490 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3490)
                 (fun uu____3493  ->
                    let uu____3494 = __tc e t  in
                    bind uu____3494
                      (fun uu____3515  ->
                         match uu____3515 with
                         | (t1,uu____3525,uu____3526) ->
                             let steps =
                               let uu____3530 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3530
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____3536  ->
                                  let uu____3537 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3537)
                               (fun uu____3539  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3473
  
let (refine_intro : unit -> unit tac) =
  fun uu____3550  ->
    let uu____3553 =
      let uu____3556 = cur_goal ()  in
      bind uu____3556
        (fun g  ->
           let uu____3563 =
             let uu____3574 = FStar_Tactics_Types.goal_env g  in
             let uu____3575 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3574 uu____3575
              in
           match uu____3563 with
           | (uu____3578,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3603 =
                 let uu____3608 =
                   let uu____3613 =
                     let uu____3614 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3614]  in
                   FStar_Syntax_Subst.open_term uu____3613 phi  in
                 match uu____3608 with
                 | (bvs,phi1) ->
                     let uu____3639 =
                       let uu____3640 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3640  in
                     (uu____3639, phi1)
                  in
               (match uu____3603 with
                | (bv1,phi1) ->
                    let uu____3659 =
                      let uu____3662 = FStar_Tactics_Types.goal_env g  in
                      let uu____3663 =
                        let uu____3664 =
                          let uu____3667 =
                            let uu____3668 =
                              let uu____3675 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3675)  in
                            FStar_Syntax_Syntax.NT uu____3668  in
                          [uu____3667]  in
                        FStar_Syntax_Subst.subst uu____3664 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3662
                        uu____3663 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3659
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3683  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3553
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3702 = cur_goal ()  in
      bind uu____3702
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3710 = FStar_Tactics_Types.goal_env goal  in
               let uu____3711 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3710 uu____3711
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3713 = __tc env t  in
           bind uu____3713
             (fun uu____3732  ->
                match uu____3732 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3747  ->
                         let uu____3748 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3749 =
                           let uu____3750 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3750
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3748 uu____3749)
                      (fun uu____3753  ->
                         let uu____3754 =
                           let uu____3757 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3757 guard  in
                         bind uu____3754
                           (fun uu____3759  ->
                              mlog
                                (fun uu____3763  ->
                                   let uu____3764 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3765 =
                                     let uu____3766 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3766
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3764 uu____3765)
                                (fun uu____3769  ->
                                   let uu____3770 =
                                     let uu____3773 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3774 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3773 typ uu____3774  in
                                   bind uu____3770
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3780 =
                                             let uu____3781 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3781 t1  in
                                           let uu____3782 =
                                             let uu____3783 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3783 typ  in
                                           let uu____3784 =
                                             let uu____3785 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3786 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3785 uu____3786  in
                                           let uu____3787 =
                                             let uu____3788 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3789 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3788 uu____3789  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3780 uu____3782 uu____3784
                                             uu____3787)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3809 =
          mlog
            (fun uu____3814  ->
               let uu____3815 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3815)
            (fun uu____3818  ->
               let uu____3819 =
                 let uu____3826 = __exact_now set_expected_typ1 tm  in
                 catch uu____3826  in
               bind uu____3819
                 (fun uu___349_3835  ->
                    match uu___349_3835 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3846  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3849  ->
                             let uu____3850 =
                               let uu____3857 =
                                 let uu____3860 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3860
                                   (fun uu____3865  ->
                                      let uu____3866 = refine_intro ()  in
                                      bind uu____3866
                                        (fun uu____3870  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3857  in
                             bind uu____3850
                               (fun uu___348_3877  ->
                                  match uu___348_3877 with
                                  | FStar_Util.Inr r -> ret ()
                                  | FStar_Util.Inl uu____3885 -> fail e))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3809
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3935 = f x  in
          bind uu____3935
            (fun y  ->
               let uu____3943 = mapM f xs  in
               bind uu____3943 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4014 = do_unify e ty1 ty2  in
          bind uu____4014
            (fun uu___350_4026  ->
               if uu___350_4026
               then ret acc
               else
                 (let uu____4045 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4045 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4066 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4067 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4066
                        uu____4067
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4082 =
                        let uu____4083 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4083  in
                      if uu____4082
                      then fail "Codomain is effectful"
                      else
                        (let uu____4103 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4103
                           (fun uu____4129  ->
                              match uu____4129 with
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
      let uu____4215 =
        mlog
          (fun uu____4220  ->
             let uu____4221 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4221)
          (fun uu____4224  ->
             let uu____4225 = cur_goal ()  in
             bind uu____4225
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4233 = __tc e tm  in
                  bind uu____4233
                    (fun uu____4254  ->
                       match uu____4254 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4267 =
                             let uu____4278 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4278  in
                           bind uu____4267
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4321  ->
                                       fun w  ->
                                         match uu____4321 with
                                         | (uvt,q,uu____4339) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4371 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4388  ->
                                       fun s  ->
                                         match uu____4388 with
                                         | (uu____4400,uu____4401,uv) ->
                                             let uu____4403 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4403) uvs uu____4371
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4412 = solve' goal w  in
                                bind uu____4412
                                  (fun uu____4417  ->
                                     let uu____4418 =
                                       mapM
                                         (fun uu____4435  ->
                                            match uu____4435 with
                                            | (uvt,q,uv) ->
                                                let uu____4447 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4447 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4452 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4453 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4453
                                                     then ret ()
                                                     else
                                                       (let uu____4457 =
                                                          let uu____4460 =
                                                            bnorm_goal
                                                              (let uu___392_4463
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___392_4463.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___392_4463.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4460]  in
                                                        add_goals uu____4457)))
                                         uvs
                                        in
                                     bind uu____4418
                                       (fun uu____4467  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4215
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4492 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4492
    then
      let uu____4499 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4514 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4567 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4499 with
      | (pre,post) ->
          let post1 =
            let uu____4599 =
              let uu____4610 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4610]  in
            FStar_Syntax_Util.mk_app post uu____4599  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4640 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4640
       then
         let uu____4647 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4647
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4680 =
      let uu____4683 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4690  ->
                  let uu____4691 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4691)
               (fun uu____4695  ->
                  let is_unit_t t =
                    let uu____4702 =
                      let uu____4703 = FStar_Syntax_Subst.compress t  in
                      uu____4703.FStar_Syntax_Syntax.n  in
                    match uu____4702 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4707 -> false  in
                  let uu____4708 = cur_goal ()  in
                  bind uu____4708
                    (fun goal  ->
                       let uu____4714 =
                         let uu____4723 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4723 tm  in
                       bind uu____4714
                         (fun uu____4738  ->
                            match uu____4738 with
                            | (tm1,t,guard) ->
                                let uu____4750 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4750 with
                                 | (bs,comp) ->
                                     let uu____4783 = lemma_or_sq comp  in
                                     (match uu____4783 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4802 =
                                            FStar_List.fold_left
                                              (fun uu____4850  ->
                                                 fun uu____4851  ->
                                                   match (uu____4850,
                                                           uu____4851)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4964 =
                                                         is_unit_t b_t  in
                                                       if uu____4964
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5002 =
                                                            let uu____5015 =
                                                              let uu____5016
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5016.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5019 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5015
                                                              uu____5019 b_t
                                                             in
                                                          match uu____5002
                                                          with
                                                          | (u,uu____5037,g_u)
                                                              ->
                                                              let uu____5051
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5051,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4802 with
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
                                               let uu____5130 =
                                                 let uu____5133 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5134 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5135 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5133
                                                   uu____5134 uu____5135
                                                  in
                                               bind uu____5130
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5143 =
                                                        let uu____5144 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5144 tm1
                                                         in
                                                      let uu____5145 =
                                                        let uu____5146 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5147 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5146
                                                          uu____5147
                                                         in
                                                      let uu____5148 =
                                                        let uu____5149 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5150 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5149
                                                          uu____5150
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5143 uu____5145
                                                        uu____5148
                                                    else
                                                      (let uu____5152 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5152
                                                         (fun uu____5157  ->
                                                            let uu____5158 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5158
                                                              (fun uu____5166
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5191
                                                                    =
                                                                    let uu____5194
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5194
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5191
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
                                                                    let uu____5229
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5229)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5245
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5245
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5263)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5289)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5306
                                                                    -> false)
                                                                    in
                                                                 let uu____5307
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
                                                                    let uu____5337
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5337
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5359)
                                                                    ->
                                                                    let uu____5384
                                                                    =
                                                                    let uu____5385
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5385.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5384
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5393)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___393_5413
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___393_5413.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___393_5413.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___393_5413.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5416
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5422
                                                                     ->
                                                                    let uu____5423
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5424
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5423
                                                                    uu____5424)
                                                                    (fun
                                                                    uu____5429
                                                                     ->
                                                                    let env =
                                                                    let uu___394_5431
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___394_5431.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5433
                                                                    =
                                                                    let uu____5436
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5437
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5438
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5437
                                                                    uu____5438
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5440
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5436
                                                                    uu____5440
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5433
                                                                    (fun
                                                                    uu____5444
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5307
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
                                                                    let uu____5506
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5506
                                                                    then
                                                                    let uu____5509
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5509
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
                                                                    let uu____5523
                                                                    =
                                                                    let uu____5524
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5524
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5523)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5525
                                                                    =
                                                                    let uu____5528
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5528
                                                                    guard  in
                                                                    bind
                                                                    uu____5525
                                                                    (fun
                                                                    uu____5531
                                                                     ->
                                                                    let uu____5532
                                                                    =
                                                                    let uu____5535
                                                                    =
                                                                    let uu____5536
                                                                    =
                                                                    let uu____5537
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5538
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5537
                                                                    uu____5538
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5536
                                                                     in
                                                                    if
                                                                    uu____5535
                                                                    then
                                                                    let uu____5541
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5541
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5532
                                                                    (fun
                                                                    uu____5544
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4683  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4680
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5566 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5566 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5576::(e1,uu____5578)::(e2,uu____5580)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5641 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5665 = destruct_eq' typ  in
    match uu____5665 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5695 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5695 with
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
        let uu____5757 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5757 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5805 = aux e'  in
               FStar_Util.map_opt uu____5805
                 (fun uu____5829  ->
                    match uu____5829 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5850 = aux e  in
      FStar_Util.map_opt uu____5850
        (fun uu____5874  ->
           match uu____5874 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5941 =
            let uu____5950 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5950  in
          FStar_Util.map_opt uu____5941
            (fun uu____5965  ->
               match uu____5965 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___395_5984 = bv  in
                     let uu____5985 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___395_5984.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___395_5984.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5985
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___396_5993 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5994 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6003 =
                       let uu____6006 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6006  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___396_5993.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5994;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6003;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___396_5993.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___396_5993.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___396_5993.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___397_6007 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___397_6007.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___397_6007.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___397_6007.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6017 =
      let uu____6020 = cur_goal ()  in
      bind uu____6020
        (fun goal  ->
           let uu____6028 = h  in
           match uu____6028 with
           | (bv,uu____6032) ->
               mlog
                 (fun uu____6040  ->
                    let uu____6041 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6042 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6041
                      uu____6042)
                 (fun uu____6045  ->
                    let uu____6046 =
                      let uu____6055 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6055  in
                    match uu____6046 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6076 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6076 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6091 =
                               let uu____6092 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6092.FStar_Syntax_Syntax.n  in
                             (match uu____6091 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___398_6109 = bv1  in
                                    let uu____6110 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___398_6109.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___398_6109.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6110
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___399_6118 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6119 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6128 =
                                      let uu____6131 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6131
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___399_6118.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6119;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6128;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___399_6118.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___399_6118.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___399_6118.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___400_6134 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___400_6134.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___400_6134.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___400_6134.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6135 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6136 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6017
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6161 =
        let uu____6164 = cur_goal ()  in
        bind uu____6164
          (fun goal  ->
             let uu____6175 = b  in
             match uu____6175 with
             | (bv,uu____6179) ->
                 let bv' =
                   let uu____6185 =
                     let uu___401_6186 = bv  in
                     let uu____6187 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6187;
                       FStar_Syntax_Syntax.index =
                         (uu___401_6186.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___401_6186.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6185  in
                 let s1 =
                   let uu____6191 =
                     let uu____6192 =
                       let uu____6199 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6199)  in
                     FStar_Syntax_Syntax.NT uu____6192  in
                   [uu____6191]  in
                 let uu____6204 = subst_goal bv bv' s1 goal  in
                 (match uu____6204 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6161
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6223 =
      let uu____6226 = cur_goal ()  in
      bind uu____6226
        (fun goal  ->
           let uu____6235 = b  in
           match uu____6235 with
           | (bv,uu____6239) ->
               let uu____6244 =
                 let uu____6253 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6253  in
               (match uu____6244 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6274 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6274 with
                     | (ty,u) ->
                         let uu____6283 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6283
                           (fun uu____6301  ->
                              match uu____6301 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___402_6311 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___402_6311.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___402_6311.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6315 =
                                      let uu____6316 =
                                        let uu____6323 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6323)  in
                                      FStar_Syntax_Syntax.NT uu____6316  in
                                    [uu____6315]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___403_6335 = b1  in
                                         let uu____6336 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___403_6335.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___403_6335.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6336
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6343  ->
                                       let new_goal =
                                         let uu____6345 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6346 =
                                           let uu____6347 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6347
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6345 uu____6346
                                          in
                                       let uu____6348 = add_goals [new_goal]
                                          in
                                       bind uu____6348
                                         (fun uu____6353  ->
                                            let uu____6354 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6354
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6223
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6377 =
        let uu____6380 = cur_goal ()  in
        bind uu____6380
          (fun goal  ->
             let uu____6389 = b  in
             match uu____6389 with
             | (bv,uu____6393) ->
                 let uu____6398 =
                   let uu____6407 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6407  in
                 (match uu____6398 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6431 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6431
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___404_6436 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___404_6436.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___404_6436.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6438 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6438))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6377
  
let (revert : unit -> unit tac) =
  fun uu____6449  ->
    let uu____6452 = cur_goal ()  in
    bind uu____6452
      (fun goal  ->
         let uu____6458 =
           let uu____6465 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6465  in
         match uu____6458 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6481 =
                 let uu____6484 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6484  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6481
                in
             let uu____6499 = new_uvar "revert" env' typ'  in
             bind uu____6499
               (fun uu____6514  ->
                  match uu____6514 with
                  | (r,u_r) ->
                      let uu____6523 =
                        let uu____6526 =
                          let uu____6527 =
                            let uu____6528 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6528.FStar_Syntax_Syntax.pos  in
                          let uu____6531 =
                            let uu____6536 =
                              let uu____6537 =
                                let uu____6546 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6546  in
                              [uu____6537]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6536  in
                          uu____6531 FStar_Pervasives_Native.None uu____6527
                           in
                        set_solution goal uu____6526  in
                      bind uu____6523
                        (fun uu____6567  ->
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
      let uu____6579 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6579
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6594 = cur_goal ()  in
    bind uu____6594
      (fun goal  ->
         mlog
           (fun uu____6602  ->
              let uu____6603 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6604 =
                let uu____6605 =
                  let uu____6606 =
                    let uu____6615 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6615  in
                  FStar_All.pipe_right uu____6606 FStar_List.length  in
                FStar_All.pipe_right uu____6605 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6603 uu____6604)
           (fun uu____6632  ->
              let uu____6633 =
                let uu____6642 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6642  in
              match uu____6633 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6681 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6681
                        then
                          let uu____6684 =
                            let uu____6685 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6685
                             in
                          fail uu____6684
                        else check1 bvs2
                     in
                  let uu____6687 =
                    let uu____6688 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6688  in
                  if uu____6687
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6692 = check1 bvs  in
                     bind uu____6692
                       (fun uu____6698  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6700 =
                            let uu____6707 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6707  in
                          bind uu____6700
                            (fun uu____6716  ->
                               match uu____6716 with
                               | (ut,uvar_ut) ->
                                   let uu____6725 = set_solution goal ut  in
                                   bind uu____6725
                                     (fun uu____6730  ->
                                        let uu____6731 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6731))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6738  ->
    let uu____6741 = cur_goal ()  in
    bind uu____6741
      (fun goal  ->
         let uu____6747 =
           let uu____6754 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6754  in
         match uu____6747 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6762) ->
             let uu____6767 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6767)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6777 = cur_goal ()  in
    bind uu____6777
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6787 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6787  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6790  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6800 = cur_goal ()  in
    bind uu____6800
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6810 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6810  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6813  -> add_goals [g']))
  
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
            let uu____6853 = FStar_Syntax_Subst.compress t  in
            uu____6853.FStar_Syntax_Syntax.n  in
          let uu____6856 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___408_6862 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___408_6862.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___408_6862.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6856
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6878 =
                   let uu____6879 = FStar_Syntax_Subst.compress t1  in
                   uu____6879.FStar_Syntax_Syntax.n  in
                 match uu____6878 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6910 = ff hd1  in
                     bind uu____6910
                       (fun hd2  ->
                          let fa uu____6936 =
                            match uu____6936 with
                            | (a,q) ->
                                let uu____6957 = ff a  in
                                bind uu____6957 (fun a1  -> ret (a1, q))
                             in
                          let uu____6976 = mapM fa args  in
                          bind uu____6976
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7058 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7058 with
                      | (bs1,t') ->
                          let uu____7067 =
                            let uu____7070 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7070 t'  in
                          bind uu____7067
                            (fun t''  ->
                               let uu____7074 =
                                 let uu____7075 =
                                   let uu____7094 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7103 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7094, uu____7103, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7075  in
                               ret uu____7074))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7178 = ff hd1  in
                     bind uu____7178
                       (fun hd2  ->
                          let ffb br =
                            let uu____7193 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7193 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7225 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7225  in
                                let uu____7226 = ff1 e  in
                                bind uu____7226
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7241 = mapM ffb brs  in
                          bind uu____7241
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7285;
                          FStar_Syntax_Syntax.lbtyp = uu____7286;
                          FStar_Syntax_Syntax.lbeff = uu____7287;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7289;
                          FStar_Syntax_Syntax.lbpos = uu____7290;_}::[]),e)
                     ->
                     let lb =
                       let uu____7315 =
                         let uu____7316 = FStar_Syntax_Subst.compress t1  in
                         uu____7316.FStar_Syntax_Syntax.n  in
                       match uu____7315 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7320) -> lb
                       | uu____7333 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7342 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7342
                         (fun def1  ->
                            ret
                              (let uu___405_7348 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___405_7348.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___405_7348.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___405_7348.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___405_7348.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___405_7348.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___405_7348.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7349 = fflb lb  in
                     bind uu____7349
                       (fun lb1  ->
                          let uu____7359 =
                            let uu____7364 =
                              let uu____7365 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7365]  in
                            FStar_Syntax_Subst.open_term uu____7364 e  in
                          match uu____7359 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7395 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7395  in
                              let uu____7396 = ff1 e1  in
                              bind uu____7396
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7437 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7437
                         (fun def  ->
                            ret
                              (let uu___406_7443 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___406_7443.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___406_7443.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___406_7443.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___406_7443.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___406_7443.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___406_7443.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7444 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7444 with
                      | (lbs1,e1) ->
                          let uu____7459 = mapM fflb lbs1  in
                          bind uu____7459
                            (fun lbs2  ->
                               let uu____7471 = ff e1  in
                               bind uu____7471
                                 (fun e2  ->
                                    let uu____7479 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7479 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7547 = ff t2  in
                     bind uu____7547
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7578 = ff t2  in
                     bind uu____7578
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7585 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___407_7592 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___407_7592.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___407_7592.FStar_Syntax_Syntax.vars)
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
            let uu____7629 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___409_7638 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___409_7638.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___409_7638.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___409_7638.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___409_7638.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___409_7638.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___409_7638.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___409_7638.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___409_7638.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___409_7638.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___409_7638.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___409_7638.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___409_7638.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___409_7638.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___409_7638.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___409_7638.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___409_7638.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___409_7638.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___409_7638.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___409_7638.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___409_7638.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___409_7638.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___409_7638.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___409_7638.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___409_7638.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___409_7638.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___409_7638.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___409_7638.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___409_7638.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___409_7638.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___409_7638.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___409_7638.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___409_7638.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___409_7638.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___409_7638.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___409_7638.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___409_7638.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___409_7638.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___409_7638.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___409_7638.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___409_7638.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___409_7638.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7629 with
            | (t1,lcomp,g) ->
                let uu____7644 =
                  (let uu____7647 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7647) ||
                    (let uu____7649 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7649)
                   in
                if uu____7644
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7657 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7657
                       (fun uu____7673  ->
                          match uu____7673 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7686  ->
                                    let uu____7687 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7688 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7687 uu____7688);
                               (let uu____7689 =
                                  let uu____7692 =
                                    let uu____7693 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7693 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7692
                                    opts
                                   in
                                bind uu____7689
                                  (fun uu____7696  ->
                                     let uu____7697 =
                                       bind tau
                                         (fun uu____7703  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7709  ->
                                                 let uu____7710 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7711 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7710 uu____7711);
                                            ret ut1)
                                        in
                                     focus uu____7697))))
                      in
                   let uu____7712 = catch rewrite_eq  in
                   bind uu____7712
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
          let uu____7910 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7910
            (fun t1  ->
               let uu____7918 =
                 f env
                   (let uu___412_7927 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___412_7927.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___412_7927.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7918
                 (fun uu____7943  ->
                    match uu____7943 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7966 =
                               let uu____7967 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7967.FStar_Syntax_Syntax.n  in
                             match uu____7966 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8004 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8004
                                   (fun uu____8029  ->
                                      match uu____8029 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8045 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8045
                                            (fun uu____8072  ->
                                               match uu____8072 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___410_8102 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___410_8102.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___410_8102.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8144 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8144 with
                                  | (bs1,t') ->
                                      let uu____8159 =
                                        let uu____8166 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8166 ctrl1 t'
                                         in
                                      bind uu____8159
                                        (fun uu____8184  ->
                                           match uu____8184 with
                                           | (t'',ctrl2) ->
                                               let uu____8199 =
                                                 let uu____8206 =
                                                   let uu___411_8209 = t4  in
                                                   let uu____8212 =
                                                     let uu____8213 =
                                                       let uu____8232 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8241 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8232,
                                                         uu____8241, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8213
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8212;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___411_8209.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___411_8209.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8206, ctrl2)  in
                                               ret uu____8199))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8294 -> ret (t3, ctrl1))))

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
              let uu____8341 = ctrl_tac_fold f env ctrl t  in
              bind uu____8341
                (fun uu____8365  ->
                   match uu____8365 with
                   | (t1,ctrl1) ->
                       let uu____8380 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8380
                         (fun uu____8407  ->
                            match uu____8407 with
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
              let uu____8491 =
                let uu____8498 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8498
                  (fun uu____8507  ->
                     let uu____8508 = ctrl t1  in
                     bind uu____8508
                       (fun res  ->
                          let uu____8531 = trivial ()  in
                          bind uu____8531 (fun uu____8539  -> ret res)))
                 in
              bind uu____8491
                (fun uu____8555  ->
                   match uu____8555 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8579 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___413_8588 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___413_8588.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___413_8588.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___413_8588.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___413_8588.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___413_8588.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___413_8588.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___413_8588.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___413_8588.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___413_8588.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___413_8588.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___413_8588.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___413_8588.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___413_8588.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___413_8588.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___413_8588.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___413_8588.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___413_8588.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___413_8588.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___413_8588.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___413_8588.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___413_8588.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___413_8588.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___413_8588.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___413_8588.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___413_8588.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___413_8588.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___413_8588.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___413_8588.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___413_8588.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___413_8588.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___413_8588.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___413_8588.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___413_8588.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___413_8588.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___413_8588.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___413_8588.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___413_8588.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___413_8588.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___413_8588.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___413_8588.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___413_8588.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8579 with
                          | (t2,lcomp,g) ->
                              let uu____8598 =
                                (let uu____8601 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8601) ||
                                  (let uu____8603 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8603)
                                 in
                              if uu____8598
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8616 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8616
                                   (fun uu____8636  ->
                                      match uu____8636 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8653  ->
                                                let uu____8654 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8655 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8654 uu____8655);
                                           (let uu____8656 =
                                              let uu____8659 =
                                                let uu____8660 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8660 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8659 opts
                                               in
                                            bind uu____8656
                                              (fun uu____8667  ->
                                                 let uu____8668 =
                                                   bind rewriter
                                                     (fun uu____8682  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8688  ->
                                                             let uu____8689 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8690 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8689
                                                               uu____8690);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8668)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8731 =
        bind get
          (fun ps  ->
             let uu____8741 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8741 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8778  ->
                       let uu____8779 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8779);
                  bind dismiss_all
                    (fun uu____8782  ->
                       let uu____8783 =
                         let uu____8790 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8790
                           keepGoing gt1
                          in
                       bind uu____8783
                         (fun uu____8802  ->
                            match uu____8802 with
                            | (gt',uu____8810) ->
                                (log ps
                                   (fun uu____8814  ->
                                      let uu____8815 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8815);
                                 (let uu____8816 = push_goals gs  in
                                  bind uu____8816
                                    (fun uu____8821  ->
                                       let uu____8822 =
                                         let uu____8825 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8825]  in
                                       add_goals uu____8822)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8731
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8848 =
        bind get
          (fun ps  ->
             let uu____8858 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8858 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8895  ->
                       let uu____8896 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8896);
                  bind dismiss_all
                    (fun uu____8899  ->
                       let uu____8900 =
                         let uu____8903 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8903 gt1
                          in
                       bind uu____8900
                         (fun gt'  ->
                            log ps
                              (fun uu____8911  ->
                                 let uu____8912 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8912);
                            (let uu____8913 = push_goals gs  in
                             bind uu____8913
                               (fun uu____8918  ->
                                  let uu____8919 =
                                    let uu____8922 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8922]  in
                                  add_goals uu____8919))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8848
  
let (trefl : unit -> unit tac) =
  fun uu____8933  ->
    let uu____8936 =
      let uu____8939 = cur_goal ()  in
      bind uu____8939
        (fun g  ->
           let uu____8957 =
             let uu____8962 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8962  in
           match uu____8957 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8970 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8970 with
                | (hd1,args) ->
                    let uu____9009 =
                      let uu____9022 =
                        let uu____9023 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9023.FStar_Syntax_Syntax.n  in
                      (uu____9022, args)  in
                    (match uu____9009 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9037::(l,uu____9039)::(r,uu____9041)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9088 =
                           let uu____9091 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9091 l r  in
                         bind uu____9088
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9098 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9098 l
                                    in
                                 let r1 =
                                   let uu____9100 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9100 r
                                    in
                                 let uu____9101 =
                                   let uu____9104 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9104 l1 r1  in
                                 bind uu____9101
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9110 =
                                           let uu____9111 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9111 l1  in
                                         let uu____9112 =
                                           let uu____9113 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9113 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9110 uu____9112))))
                     | (hd2,uu____9115) ->
                         let uu____9132 =
                           let uu____9133 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9133 t  in
                         fail1 "trefl: not an equality (%s)" uu____9132))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8936
  
let (dup : unit -> unit tac) =
  fun uu____9146  ->
    let uu____9149 = cur_goal ()  in
    bind uu____9149
      (fun g  ->
         let uu____9155 =
           let uu____9162 = FStar_Tactics_Types.goal_env g  in
           let uu____9163 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9162 uu____9163  in
         bind uu____9155
           (fun uu____9172  ->
              match uu____9172 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___414_9182 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___414_9182.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___414_9182.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___414_9182.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9185  ->
                       let uu____9186 =
                         let uu____9189 = FStar_Tactics_Types.goal_env g  in
                         let uu____9190 =
                           let uu____9191 =
                             let uu____9192 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9193 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9192
                               uu____9193
                              in
                           let uu____9194 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9195 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9191 uu____9194 u
                             uu____9195
                            in
                         add_irrelevant_goal "dup equation" uu____9189
                           uu____9190 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9186
                         (fun uu____9198  ->
                            let uu____9199 = add_goals [g']  in
                            bind uu____9199 (fun uu____9203  -> ret ())))))
  
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
              let uu____9326 = f x y  in
              if uu____9326 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9346 -> (acc, l11, l21)  in
        let uu____9361 = aux [] l1 l2  in
        match uu____9361 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9466 = get_phi g1  in
      match uu____9466 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9472 = get_phi g2  in
          (match uu____9472 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9484 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9484 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9515 =
                        FStar_TypeChecker_Env.binders_of_bindings r1  in
                      close_forall_no_univs1 uu____9515 phi1  in
                    let t2 =
                      let uu____9525 =
                        FStar_TypeChecker_Env.binders_of_bindings r2  in
                      close_forall_no_univs1 uu____9525 phi2  in
                    let uu____9534 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9534
                      (fun uu____9539  ->
                         let uu____9540 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9540
                           (fun uu____9547  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___415_9552 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9553 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___415_9552.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___415_9552.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___415_9552.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___415_9552.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9553;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___415_9552.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___415_9552.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___415_9552.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___415_9552.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___415_9552.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___415_9552.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___415_9552.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___415_9552.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___415_9552.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___415_9552.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___415_9552.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___415_9552.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___415_9552.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___415_9552.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___415_9552.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___415_9552.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___415_9552.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___415_9552.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___415_9552.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___415_9552.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___415_9552.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___415_9552.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___415_9552.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___415_9552.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___415_9552.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___415_9552.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___415_9552.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___415_9552.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___415_9552.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___415_9552.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___415_9552.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___415_9552.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___415_9552.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___415_9552.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___415_9552.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___415_9552.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9556 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9556
                                (fun goal  ->
                                   mlog
                                     (fun uu____9565  ->
                                        let uu____9566 =
                                          goal_to_string_verbose g1  in
                                        let uu____9567 =
                                          goal_to_string_verbose g2  in
                                        let uu____9568 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9566 uu____9567 uu____9568)
                                     (fun uu____9570  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9577  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9593 =
               set
                 (let uu___416_9598 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___416_9598.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___416_9598.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___416_9598.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___416_9598.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___416_9598.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___416_9598.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___416_9598.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___416_9598.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___416_9598.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___416_9598.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___416_9598.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___416_9598.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9593
               (fun uu____9601  ->
                  let uu____9602 = join_goals g1 g2  in
                  bind uu____9602 (fun g12  -> add_goals [g12]))
         | uu____9607 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9627 =
      let uu____9634 = cur_goal ()  in
      bind uu____9634
        (fun g  ->
           let uu____9644 =
             let uu____9653 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9653 t  in
           bind uu____9644
             (fun uu____9681  ->
                match uu____9681 with
                | (t1,typ,guard) ->
                    let uu____9697 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9697 with
                     | (hd1,args) ->
                         let uu____9746 =
                           let uu____9761 =
                             let uu____9762 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9762.FStar_Syntax_Syntax.n  in
                           (uu____9761, args)  in
                         (match uu____9746 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9783)::(q,uu____9785)::[]) when
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
                                let uu____9839 =
                                  let uu____9840 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9840
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9839
                                 in
                              let g2 =
                                let uu____9842 =
                                  let uu____9843 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9843
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9842
                                 in
                              bind __dismiss
                                (fun uu____9850  ->
                                   let uu____9851 = add_goals [g1; g2]  in
                                   bind uu____9851
                                     (fun uu____9860  ->
                                        let uu____9861 =
                                          let uu____9866 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9867 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9866, uu____9867)  in
                                        ret uu____9861))
                          | uu____9872 ->
                              let uu____9887 =
                                let uu____9888 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9888 typ  in
                              fail1 "Not a disjunction: %s" uu____9887))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9627
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9918 =
      let uu____9921 = cur_goal ()  in
      bind uu____9921
        (fun g  ->
           FStar_Options.push ();
           (let uu____9934 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9934);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___417_9941 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___417_9941.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___417_9941.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___417_9941.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9918
  
let (top_env : unit -> env tac) =
  fun uu____9953  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9966  ->
    let uu____9969 = cur_goal ()  in
    bind uu____9969
      (fun g  ->
         let uu____9975 =
           (FStar_Options.lax ()) ||
             (let uu____9977 = FStar_Tactics_Types.goal_env g  in
              uu____9977.FStar_TypeChecker_Env.lax)
            in
         ret uu____9975)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9992 =
        mlog
          (fun uu____9997  ->
             let uu____9998 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9998)
          (fun uu____10001  ->
             let uu____10002 = cur_goal ()  in
             bind uu____10002
               (fun goal  ->
                  let env =
                    let uu____10010 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10010 ty  in
                  let uu____10011 = __tc_ghost env tm  in
                  bind uu____10011
                    (fun uu____10030  ->
                       match uu____10030 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10044  ->
                                let uu____10045 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10045)
                             (fun uu____10047  ->
                                mlog
                                  (fun uu____10050  ->
                                     let uu____10051 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10051)
                                  (fun uu____10054  ->
                                     let uu____10055 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10055
                                       (fun uu____10059  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9992
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10082 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10088 =
              let uu____10095 =
                let uu____10096 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10096
                 in
              new_uvar "uvar_env.2" env uu____10095  in
            bind uu____10088
              (fun uu____10112  ->
                 match uu____10112 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10082
        (fun typ  ->
           let uu____10124 = new_uvar "uvar_env" env typ  in
           bind uu____10124
             (fun uu____10138  ->
                match uu____10138 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10156 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10175 -> g.FStar_Tactics_Types.opts
             | uu____10178 -> FStar_Options.peek ()  in
           let uu____10181 = FStar_Syntax_Util.head_and_args t  in
           match uu____10181 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10201);
                FStar_Syntax_Syntax.pos = uu____10202;
                FStar_Syntax_Syntax.vars = uu____10203;_},uu____10204)
               ->
               let env1 =
                 let uu___418_10246 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___418_10246.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___418_10246.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___418_10246.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___418_10246.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___418_10246.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___418_10246.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___418_10246.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___418_10246.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___418_10246.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___418_10246.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___418_10246.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___418_10246.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___418_10246.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___418_10246.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___418_10246.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___418_10246.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___418_10246.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___418_10246.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___418_10246.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___418_10246.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___418_10246.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___418_10246.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___418_10246.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___418_10246.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___418_10246.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___418_10246.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___418_10246.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___418_10246.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___418_10246.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___418_10246.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___418_10246.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___418_10246.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___418_10246.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___418_10246.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___418_10246.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___418_10246.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___418_10246.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___418_10246.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___418_10246.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___418_10246.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___418_10246.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10248 =
                 let uu____10251 = bnorm_goal g  in [uu____10251]  in
               add_goals uu____10248
           | uu____10252 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10156
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10301 = if b then t2 else ret false  in
             bind uu____10301 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10312 = trytac comp  in
      bind uu____10312
        (fun uu___351_10320  ->
           match uu___351_10320 with
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
        let uu____10346 =
          bind get
            (fun ps  ->
               let uu____10352 = __tc e t1  in
               bind uu____10352
                 (fun uu____10372  ->
                    match uu____10372 with
                    | (t11,ty1,g1) ->
                        let uu____10384 = __tc e t2  in
                        bind uu____10384
                          (fun uu____10404  ->
                             match uu____10404 with
                             | (t21,ty2,g2) ->
                                 let uu____10416 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10416
                                   (fun uu____10421  ->
                                      let uu____10422 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10422
                                        (fun uu____10428  ->
                                           let uu____10429 =
                                             do_unify e ty1 ty2  in
                                           let uu____10432 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10429 uu____10432)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10346
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10465  ->
             let uu____10466 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10466
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
        (fun uu____10487  ->
           let uu____10488 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10488)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10498 =
      mlog
        (fun uu____10503  ->
           let uu____10504 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10504)
        (fun uu____10507  ->
           let uu____10508 = cur_goal ()  in
           bind uu____10508
             (fun g  ->
                let uu____10514 =
                  let uu____10523 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10523 ty  in
                bind uu____10514
                  (fun uu____10535  ->
                     match uu____10535 with
                     | (ty1,uu____10545,guard) ->
                         let uu____10547 =
                           let uu____10550 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10550 guard  in
                         bind uu____10547
                           (fun uu____10553  ->
                              let uu____10554 =
                                let uu____10557 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10558 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10557 uu____10558 ty1  in
                              bind uu____10554
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10564 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10564
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10570 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10571 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10570
                                          uu____10571
                                         in
                                      let nty =
                                        let uu____10573 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10573 ty1  in
                                      let uu____10574 =
                                        let uu____10577 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10577 ng nty  in
                                      bind uu____10574
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10583 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10583
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10498
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10646 =
      let uu____10655 = cur_goal ()  in
      bind uu____10655
        (fun g  ->
           let uu____10667 =
             let uu____10676 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10676 s_tm  in
           bind uu____10667
             (fun uu____10694  ->
                match uu____10694 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10712 =
                      let uu____10715 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10715 guard  in
                    bind uu____10712
                      (fun uu____10727  ->
                         let uu____10728 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10728 with
                         | (h,args) ->
                             let uu____10773 =
                               let uu____10780 =
                                 let uu____10781 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10781.FStar_Syntax_Syntax.n  in
                               match uu____10780 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10796;
                                      FStar_Syntax_Syntax.vars = uu____10797;_},us)
                                   -> ret (fv, us)
                               | uu____10807 -> fail "type is not an fv"  in
                             bind uu____10773
                               (fun uu____10827  ->
                                  match uu____10827 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10843 =
                                        let uu____10846 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10846 t_lid
                                         in
                                      (match uu____10843 with
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
                                                  (fun uu____10895  ->
                                                     let uu____10896 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10896 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10911 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10939
                                                                  =
                                                                  let uu____10942
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10942
                                                                    c_lid
                                                                   in
                                                                match uu____10939
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
                                                                    uu____11012
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
                                                                    let uu____11017
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11017
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11040
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11040
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11083
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11083
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11156
                                                                    =
                                                                    let uu____11157
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11157
                                                                     in
                                                                    failwhen
                                                                    uu____11156
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11174
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
                                                                    uu___352_11190
                                                                    =
                                                                    match uu___352_11190
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11193)
                                                                    -> true
                                                                    | 
                                                                    uu____11194
                                                                    -> false
                                                                     in
                                                                    let uu____11197
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11197
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
                                                                    uu____11330
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
                                                                    uu____11392
                                                                     ->
                                                                    match uu____11392
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11412),
                                                                    (t,uu____11414))
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
                                                                    uu____11482
                                                                     ->
                                                                    match uu____11482
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11508),
                                                                    (t,uu____11510))
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
                                                                    uu____11565
                                                                     ->
                                                                    match uu____11565
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
                                                                    let uu____11615
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___419_11632
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___419_11632.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11615
                                                                    with
                                                                    | 
                                                                    (uu____11645,uu____11646,uu____11647,pat_t,uu____11649,uu____11650)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11656
                                                                    =
                                                                    let uu____11657
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11657
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11656
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11661
                                                                    =
                                                                    let uu____11670
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11670]
                                                                     in
                                                                    let uu____11689
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11661
                                                                    uu____11689
                                                                     in
                                                                    let nty =
                                                                    let uu____11695
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11695
                                                                     in
                                                                    let uu____11698
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11698
                                                                    (fun
                                                                    uu____11727
                                                                     ->
                                                                    match uu____11727
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
                                                                    let uu____11753
                                                                    =
                                                                    let uu____11764
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11764]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11753
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11800
                                                                    =
                                                                    let uu____11811
                                                                    =
                                                                    let uu____11816
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11816)
                                                                     in
                                                                    (g', br,
                                                                    uu____11811)
                                                                     in
                                                                    ret
                                                                    uu____11800))))))
                                                                    | 
                                                                    uu____11837
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10911
                                                           (fun goal_brs  ->
                                                              let uu____11886
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11886
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
                                                                  let uu____11959
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11959
                                                                    (
                                                                    fun
                                                                    uu____11970
                                                                     ->
                                                                    let uu____11971
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11971
                                                                    (fun
                                                                    uu____11981
                                                                     ->
                                                                    ret infos))))
                                            | uu____11988 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10646
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12033::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12061 = init xs  in x :: uu____12061
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12073 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12082) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12147 = last args  in
          (match uu____12147 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12177 =
                 let uu____12178 =
                   let uu____12183 =
                     let uu____12184 =
                       let uu____12189 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12189  in
                     uu____12184 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12183, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12178  in
               FStar_All.pipe_left ret uu____12177)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12202,uu____12203) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12255 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12255 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12296 =
                      let uu____12297 =
                        let uu____12302 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12302)  in
                      FStar_Reflection_Data.Tv_Abs uu____12297  in
                    FStar_All.pipe_left ret uu____12296))
      | FStar_Syntax_Syntax.Tm_type uu____12305 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12329 ->
          let uu____12344 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12344 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12374 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12374 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12427 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12439 =
            let uu____12440 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12440  in
          FStar_All.pipe_left ret uu____12439
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12461 =
            let uu____12462 =
              let uu____12467 =
                let uu____12468 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12468  in
              (uu____12467, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12462  in
          FStar_All.pipe_left ret uu____12461
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12502 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12507 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12507 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12560 ->
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
             | FStar_Util.Inr uu____12594 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12598 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12598 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12618 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12622 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12676 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12676
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12695 =
                  let uu____12702 =
                    FStar_List.map
                      (fun uu____12714  ->
                         match uu____12714 with
                         | (p1,uu____12722) -> inspect_pat p1) ps
                     in
                  (fv, uu____12702)  in
                FStar_Reflection_Data.Pat_Cons uu____12695
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
              (fun uu___353_12816  ->
                 match uu___353_12816 with
                 | (pat,uu____12838,t5) ->
                     let uu____12856 = inspect_pat pat  in (uu____12856, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12865 ->
          ((let uu____12867 =
              let uu____12872 =
                let uu____12873 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12874 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12873 uu____12874
                 in
              (FStar_Errors.Warning_CantInspect, uu____12872)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12867);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12073
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12887 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12887
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12891 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12891
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12895 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12895
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12902 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12902
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12927 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12927
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12944 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12944
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12963 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12963
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12967 =
          let uu____12968 =
            let uu____12975 =
              let uu____12976 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12976  in
            FStar_Syntax_Syntax.mk uu____12975  in
          uu____12968 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12967
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12984 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12984
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12993 =
          let uu____12994 =
            let uu____13001 =
              let uu____13002 =
                let uu____13015 =
                  let uu____13018 =
                    let uu____13019 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13019]  in
                  FStar_Syntax_Subst.close uu____13018 t2  in
                ((false, [lb]), uu____13015)  in
              FStar_Syntax_Syntax.Tm_let uu____13002  in
            FStar_Syntax_Syntax.mk uu____13001  in
          uu____12994 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12993
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13059 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13059 with
         | (lbs,body) ->
             let uu____13074 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13074)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13108 =
                let uu____13109 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13109  in
              FStar_All.pipe_left wrap uu____13108
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13116 =
                let uu____13117 =
                  let uu____13130 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13146 = pack_pat p1  in
                         (uu____13146, false)) ps
                     in
                  (fv, uu____13130)  in
                FStar_Syntax_Syntax.Pat_cons uu____13117  in
              FStar_All.pipe_left wrap uu____13116
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
            (fun uu___354_13192  ->
               match uu___354_13192 with
               | (pat,t1) ->
                   let uu____13209 = pack_pat pat  in
                   (uu____13209, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13257 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13257
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13285 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13285
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13331 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13331
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13370 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13370
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13387 =
        bind get
          (fun ps  ->
             let uu____13393 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13393 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13387
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13422 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___420_13429 = ps  in
                 let uu____13430 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___420_13429.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___420_13429.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___420_13429.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___420_13429.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___420_13429.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___420_13429.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___420_13429.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___420_13429.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___420_13429.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___420_13429.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___420_13429.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___420_13429.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13430
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13422
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13455 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13455 with
      | (u,ctx_uvars,g_u) ->
          let uu____13487 = FStar_List.hd ctx_uvars  in
          (match uu____13487 with
           | (ctx_uvar,uu____13501) ->
               let g =
                 let uu____13503 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13503 false
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
        let uu____13523 = goal_of_goal_ty env typ  in
        match uu____13523 with
        | (g,g_u) ->
            let ps =
              let uu____13535 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13536 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13535;
                FStar_Tactics_Types.local_state = uu____13536
              }  in
            let uu____13543 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13543)
  