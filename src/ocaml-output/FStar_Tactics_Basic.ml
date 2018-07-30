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
                                  | FStar_Util.Inr r -> ret ()
                                  | FStar_Util.Inl uu____4020 -> fail e))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3944
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4070 = f x  in
          bind uu____4070
            (fun y  ->
               let uu____4078 = mapM f xs  in
               bind uu____4078 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4149 = do_unify e ty1 ty2  in
          bind uu____4149
            (fun uu___350_4161  ->
               if uu___350_4161
               then ret acc
               else
                 (let uu____4180 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4180 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4201 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4202 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4201
                        uu____4202
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4217 =
                        let uu____4218 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4218  in
                      if uu____4217
                      then fail "Codomain is effectful"
                      else
                        (let uu____4238 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4238
                           (fun uu____4264  ->
                              match uu____4264 with
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
      let uu____4350 =
        mlog
          (fun uu____4355  ->
             let uu____4356 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4356)
          (fun uu____4359  ->
             let uu____4360 = cur_goal ()  in
             bind uu____4360
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4368 = __tc e tm  in
                  bind uu____4368
                    (fun uu____4389  ->
                       match uu____4389 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4402 =
                             let uu____4413 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4413  in
                           bind uu____4402
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4456  ->
                                       fun w  ->
                                         match uu____4456 with
                                         | (uvt,q,uu____4474) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4506 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4523  ->
                                       fun s  ->
                                         match uu____4523 with
                                         | (uu____4535,uu____4536,uv) ->
                                             let uu____4538 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4538) uvs uu____4506
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4547 = solve' goal w  in
                                bind uu____4547
                                  (fun uu____4552  ->
                                     let uu____4553 =
                                       mapM
                                         (fun uu____4570  ->
                                            match uu____4570 with
                                            | (uvt,q,uv) ->
                                                let uu____4582 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4582 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4587 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4588 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4588
                                                     then ret ()
                                                     else
                                                       (let uu____4592 =
                                                          let uu____4595 =
                                                            bnorm_goal
                                                              (let uu___396_4598
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___396_4598.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___396_4598.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4595]  in
                                                        add_goals uu____4592)))
                                         uvs
                                        in
                                     bind uu____4553
                                       (fun uu____4602  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4350
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4627 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4627
    then
      let uu____4634 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4649 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4702 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4634 with
      | (pre,post) ->
          let post1 =
            let uu____4734 =
              let uu____4745 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4745]  in
            FStar_Syntax_Util.mk_app post uu____4734  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4775 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4775
       then
         let uu____4782 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4782
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4815 =
      let uu____4818 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4825  ->
                  let uu____4826 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4826)
               (fun uu____4830  ->
                  let is_unit_t t =
                    let uu____4837 =
                      let uu____4838 = FStar_Syntax_Subst.compress t  in
                      uu____4838.FStar_Syntax_Syntax.n  in
                    match uu____4837 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4842 -> false  in
                  let uu____4843 = cur_goal ()  in
                  bind uu____4843
                    (fun goal  ->
                       let uu____4849 =
                         let uu____4858 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4858 tm  in
                       bind uu____4849
                         (fun uu____4873  ->
                            match uu____4873 with
                            | (tm1,t,guard) ->
                                let uu____4885 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4885 with
                                 | (bs,comp) ->
                                     let uu____4918 = lemma_or_sq comp  in
                                     (match uu____4918 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4937 =
                                            FStar_List.fold_left
                                              (fun uu____4985  ->
                                                 fun uu____4986  ->
                                                   match (uu____4985,
                                                           uu____4986)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5099 =
                                                         is_unit_t b_t  in
                                                       if uu____5099
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5137 =
                                                            let uu____5150 =
                                                              let uu____5151
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5151.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5154 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5150
                                                              uu____5154 b_t
                                                             in
                                                          match uu____5137
                                                          with
                                                          | (u,uu____5172,g_u)
                                                              ->
                                                              let uu____5186
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5186,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4937 with
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
                                               let uu____5265 =
                                                 let uu____5268 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5269 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5270 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5268
                                                   uu____5269 uu____5270
                                                  in
                                               bind uu____5265
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5278 =
                                                        let uu____5279 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5279 tm1
                                                         in
                                                      let uu____5280 =
                                                        let uu____5281 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5282 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5281
                                                          uu____5282
                                                         in
                                                      let uu____5283 =
                                                        let uu____5284 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5285 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5284
                                                          uu____5285
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5278 uu____5280
                                                        uu____5283
                                                    else
                                                      (let uu____5287 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5287
                                                         (fun uu____5292  ->
                                                            let uu____5293 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5293
                                                              (fun uu____5301
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5326
                                                                    =
                                                                    let uu____5329
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5329
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5326
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
                                                                    let uu____5364
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5364)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5380
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5380
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5398)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5424)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5441
                                                                    -> false)
                                                                    in
                                                                 let uu____5442
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
                                                                    let uu____5472
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5472
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5494)
                                                                    ->
                                                                    let uu____5519
                                                                    =
                                                                    let uu____5520
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5520.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5519
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5528)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___397_5548
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___397_5548.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___397_5548.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___397_5548.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5551
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5557
                                                                     ->
                                                                    let uu____5558
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5559
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5558
                                                                    uu____5559)
                                                                    (fun
                                                                    uu____5564
                                                                     ->
                                                                    let env =
                                                                    let uu___398_5566
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___398_5566.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5568
                                                                    =
                                                                    let uu____5571
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5572
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5573
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5572
                                                                    uu____5573
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5575
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5571
                                                                    uu____5575
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5568
                                                                    (fun
                                                                    uu____5579
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5442
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
                                                                    let uu____5641
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5641
                                                                    then
                                                                    let uu____5644
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5644
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
                                                                    let uu____5658
                                                                    =
                                                                    let uu____5659
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5659
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5658)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5660
                                                                    =
                                                                    let uu____5663
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5663
                                                                    guard  in
                                                                    bind
                                                                    uu____5660
                                                                    (fun
                                                                    uu____5666
                                                                     ->
                                                                    let uu____5667
                                                                    =
                                                                    let uu____5670
                                                                    =
                                                                    let uu____5671
                                                                    =
                                                                    let uu____5672
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5673
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5672
                                                                    uu____5673
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5671
                                                                     in
                                                                    if
                                                                    uu____5670
                                                                    then
                                                                    let uu____5676
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5676
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5667
                                                                    (fun
                                                                    uu____5679
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4818  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4815
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5701 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5701 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5711::(e1,uu____5713)::(e2,uu____5715)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5776 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5800 = destruct_eq' typ  in
    match uu____5800 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5830 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5830 with
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
        let uu____5892 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5892 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5940 = aux e'  in
               FStar_Util.map_opt uu____5940
                 (fun uu____5964  ->
                    match uu____5964 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5985 = aux e  in
      FStar_Util.map_opt uu____5985
        (fun uu____6009  ->
           match uu____6009 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____6076 =
            let uu____6085 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6085  in
          FStar_Util.map_opt uu____6076
            (fun uu____6100  ->
               match uu____6100 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___399_6119 = bv  in
                     let uu____6120 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___399_6119.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___399_6119.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6120
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___400_6128 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6129 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6138 =
                       let uu____6141 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6141  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___400_6128.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6129;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6138;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___400_6128.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___400_6128.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___400_6128.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___401_6142 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___401_6142.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___401_6142.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___401_6142.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6152 =
      let uu____6155 = cur_goal ()  in
      bind uu____6155
        (fun goal  ->
           let uu____6163 = h  in
           match uu____6163 with
           | (bv,uu____6167) ->
               mlog
                 (fun uu____6175  ->
                    let uu____6176 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6177 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6176
                      uu____6177)
                 (fun uu____6180  ->
                    let uu____6181 =
                      let uu____6190 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6190  in
                    match uu____6181 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6211 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6211 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6226 =
                               let uu____6227 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6227.FStar_Syntax_Syntax.n  in
                             (match uu____6226 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___402_6244 = bv1  in
                                    let uu____6245 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___402_6244.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___402_6244.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6245
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___403_6253 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6254 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6263 =
                                      let uu____6266 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6266
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___403_6253.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6254;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6263;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___403_6253.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___403_6253.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___403_6253.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___404_6269 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___404_6269.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___404_6269.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___404_6269.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6270 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6271 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6152
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6296 =
        let uu____6299 = cur_goal ()  in
        bind uu____6299
          (fun goal  ->
             let uu____6310 = b  in
             match uu____6310 with
             | (bv,uu____6314) ->
                 let bv' =
                   let uu____6320 =
                     let uu___405_6321 = bv  in
                     let uu____6322 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6322;
                       FStar_Syntax_Syntax.index =
                         (uu___405_6321.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___405_6321.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6320  in
                 let s1 =
                   let uu____6326 =
                     let uu____6327 =
                       let uu____6334 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6334)  in
                     FStar_Syntax_Syntax.NT uu____6327  in
                   [uu____6326]  in
                 let uu____6339 = subst_goal bv bv' s1 goal  in
                 (match uu____6339 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6296
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6358 =
      let uu____6361 = cur_goal ()  in
      bind uu____6361
        (fun goal  ->
           let uu____6370 = b  in
           match uu____6370 with
           | (bv,uu____6374) ->
               let uu____6379 =
                 let uu____6388 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6388  in
               (match uu____6379 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6409 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6409 with
                     | (ty,u) ->
                         let uu____6418 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6418
                           (fun uu____6436  ->
                              match uu____6436 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___406_6446 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___406_6446.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___406_6446.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6450 =
                                      let uu____6451 =
                                        let uu____6458 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6458)  in
                                      FStar_Syntax_Syntax.NT uu____6451  in
                                    [uu____6450]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___407_6470 = b1  in
                                         let uu____6471 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___407_6470.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___407_6470.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6471
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6478  ->
                                       let new_goal =
                                         let uu____6480 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6481 =
                                           let uu____6482 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6482
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6480 uu____6481
                                          in
                                       let uu____6483 = add_goals [new_goal]
                                          in
                                       bind uu____6483
                                         (fun uu____6488  ->
                                            let uu____6489 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6489
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6358
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6512 =
        let uu____6515 = cur_goal ()  in
        bind uu____6515
          (fun goal  ->
             let uu____6524 = b  in
             match uu____6524 with
             | (bv,uu____6528) ->
                 let uu____6533 =
                   let uu____6542 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6542  in
                 (match uu____6533 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6566 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6566
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___408_6571 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___408_6571.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___408_6571.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6573 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6573))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6512
  
let (revert : unit -> unit tac) =
  fun uu____6584  ->
    let uu____6587 = cur_goal ()  in
    bind uu____6587
      (fun goal  ->
         let uu____6593 =
           let uu____6600 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6600  in
         match uu____6593 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6616 =
                 let uu____6619 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6619  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6616
                in
             let uu____6634 = new_uvar "revert" env' typ'  in
             bind uu____6634
               (fun uu____6649  ->
                  match uu____6649 with
                  | (r,u_r) ->
                      let uu____6658 =
                        let uu____6661 =
                          let uu____6662 =
                            let uu____6663 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6663.FStar_Syntax_Syntax.pos  in
                          let uu____6666 =
                            let uu____6671 =
                              let uu____6672 =
                                let uu____6681 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6681  in
                              [uu____6672]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6671  in
                          uu____6666 FStar_Pervasives_Native.None uu____6662
                           in
                        set_solution goal uu____6661  in
                      bind uu____6658
                        (fun uu____6702  ->
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
      let uu____6714 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6714
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6729 = cur_goal ()  in
    bind uu____6729
      (fun goal  ->
         mlog
           (fun uu____6737  ->
              let uu____6738 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6739 =
                let uu____6740 =
                  let uu____6741 =
                    let uu____6750 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6750  in
                  FStar_All.pipe_right uu____6741 FStar_List.length  in
                FStar_All.pipe_right uu____6740 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6738 uu____6739)
           (fun uu____6767  ->
              let uu____6768 =
                let uu____6777 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6777  in
              match uu____6768 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6816 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6816
                        then
                          let uu____6819 =
                            let uu____6820 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6820
                             in
                          fail uu____6819
                        else check1 bvs2
                     in
                  let uu____6822 =
                    let uu____6823 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6823  in
                  if uu____6822
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6827 = check1 bvs  in
                     bind uu____6827
                       (fun uu____6833  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6835 =
                            let uu____6842 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6842  in
                          bind uu____6835
                            (fun uu____6851  ->
                               match uu____6851 with
                               | (ut,uvar_ut) ->
                                   let uu____6860 = set_solution goal ut  in
                                   bind uu____6860
                                     (fun uu____6865  ->
                                        let uu____6866 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6866))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6873  ->
    let uu____6876 = cur_goal ()  in
    bind uu____6876
      (fun goal  ->
         let uu____6882 =
           let uu____6889 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6889  in
         match uu____6882 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6897) ->
             let uu____6902 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6902)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6912 = cur_goal ()  in
    bind uu____6912
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6922 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6922  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6925  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6935 = cur_goal ()  in
    bind uu____6935
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6945 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6945  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6948  -> add_goals [g']))
  
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
            let uu____6988 = FStar_Syntax_Subst.compress t  in
            uu____6988.FStar_Syntax_Syntax.n  in
          let uu____6991 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___412_6997 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___412_6997.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___412_6997.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6991
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7013 =
                   let uu____7014 = FStar_Syntax_Subst.compress t1  in
                   uu____7014.FStar_Syntax_Syntax.n  in
                 match uu____7013 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____7045 = ff hd1  in
                     bind uu____7045
                       (fun hd2  ->
                          let fa uu____7071 =
                            match uu____7071 with
                            | (a,q) ->
                                let uu____7092 = ff a  in
                                bind uu____7092 (fun a1  -> ret (a1, q))
                             in
                          let uu____7111 = mapM fa args  in
                          bind uu____7111
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7193 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7193 with
                      | (bs1,t') ->
                          let uu____7202 =
                            let uu____7205 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7205 t'  in
                          bind uu____7202
                            (fun t''  ->
                               let uu____7209 =
                                 let uu____7210 =
                                   let uu____7229 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7238 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7229, uu____7238, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7210  in
                               ret uu____7209))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7313 = ff hd1  in
                     bind uu____7313
                       (fun hd2  ->
                          let ffb br =
                            let uu____7328 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7328 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7360 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7360  in
                                let uu____7361 = ff1 e  in
                                bind uu____7361
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7376 = mapM ffb brs  in
                          bind uu____7376
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7420;
                          FStar_Syntax_Syntax.lbtyp = uu____7421;
                          FStar_Syntax_Syntax.lbeff = uu____7422;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7424;
                          FStar_Syntax_Syntax.lbpos = uu____7425;_}::[]),e)
                     ->
                     let lb =
                       let uu____7450 =
                         let uu____7451 = FStar_Syntax_Subst.compress t1  in
                         uu____7451.FStar_Syntax_Syntax.n  in
                       match uu____7450 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7455) -> lb
                       | uu____7468 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7477 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7477
                         (fun def1  ->
                            ret
                              (let uu___409_7483 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___409_7483.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___409_7483.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___409_7483.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___409_7483.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___409_7483.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___409_7483.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7484 = fflb lb  in
                     bind uu____7484
                       (fun lb1  ->
                          let uu____7494 =
                            let uu____7499 =
                              let uu____7500 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7500]  in
                            FStar_Syntax_Subst.open_term uu____7499 e  in
                          match uu____7494 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7530 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7530  in
                              let uu____7531 = ff1 e1  in
                              bind uu____7531
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7572 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7572
                         (fun def  ->
                            ret
                              (let uu___410_7578 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___410_7578.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___410_7578.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___410_7578.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___410_7578.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___410_7578.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___410_7578.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7579 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7579 with
                      | (lbs1,e1) ->
                          let uu____7594 = mapM fflb lbs1  in
                          bind uu____7594
                            (fun lbs2  ->
                               let uu____7606 = ff e1  in
                               bind uu____7606
                                 (fun e2  ->
                                    let uu____7614 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7614 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7682 = ff t2  in
                     bind uu____7682
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7713 = ff t2  in
                     bind uu____7713
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7720 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___411_7727 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___411_7727.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___411_7727.FStar_Syntax_Syntax.vars)
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
            let uu____7764 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___413_7773 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___413_7773.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___413_7773.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___413_7773.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___413_7773.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___413_7773.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___413_7773.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___413_7773.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___413_7773.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___413_7773.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___413_7773.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___413_7773.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___413_7773.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___413_7773.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___413_7773.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___413_7773.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___413_7773.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___413_7773.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___413_7773.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___413_7773.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___413_7773.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___413_7773.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___413_7773.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___413_7773.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___413_7773.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___413_7773.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___413_7773.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___413_7773.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___413_7773.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___413_7773.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___413_7773.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___413_7773.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___413_7773.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___413_7773.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___413_7773.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___413_7773.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___413_7773.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___413_7773.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___413_7773.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___413_7773.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___413_7773.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___413_7773.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7764 with
            | (t1,lcomp,g) ->
                let uu____7779 =
                  (let uu____7782 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7782) ||
                    (let uu____7784 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7784)
                   in
                if uu____7779
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7792 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7792
                       (fun uu____7808  ->
                          match uu____7808 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7821  ->
                                    let uu____7822 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7823 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7822 uu____7823);
                               (let uu____7824 =
                                  let uu____7827 =
                                    let uu____7828 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7828 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7827
                                    opts
                                   in
                                bind uu____7824
                                  (fun uu____7831  ->
                                     let uu____7832 =
                                       bind tau
                                         (fun uu____7838  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7844  ->
                                                 let uu____7845 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7846 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7845 uu____7846);
                                            ret ut1)
                                        in
                                     focus uu____7832))))
                      in
                   let uu____7847 = catch rewrite_eq  in
                   bind uu____7847
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
          let uu____8045 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____8045
            (fun t1  ->
               let uu____8053 =
                 f env
                   (let uu___416_8062 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___416_8062.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___416_8062.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____8053
                 (fun uu____8078  ->
                    match uu____8078 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____8101 =
                               let uu____8102 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____8102.FStar_Syntax_Syntax.n  in
                             match uu____8101 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8139 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8139
                                   (fun uu____8164  ->
                                      match uu____8164 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8180 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8180
                                            (fun uu____8207  ->
                                               match uu____8207 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___414_8237 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___414_8237.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___414_8237.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8279 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8279 with
                                  | (bs1,t') ->
                                      let uu____8294 =
                                        let uu____8301 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8301 ctrl1 t'
                                         in
                                      bind uu____8294
                                        (fun uu____8319  ->
                                           match uu____8319 with
                                           | (t'',ctrl2) ->
                                               let uu____8334 =
                                                 let uu____8341 =
                                                   let uu___415_8344 = t4  in
                                                   let uu____8347 =
                                                     let uu____8348 =
                                                       let uu____8367 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8376 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8367,
                                                         uu____8376, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8348
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8347;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___415_8344.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___415_8344.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8341, ctrl2)  in
                                               ret uu____8334))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8429 -> ret (t3, ctrl1))))

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
              let uu____8476 = ctrl_tac_fold f env ctrl t  in
              bind uu____8476
                (fun uu____8500  ->
                   match uu____8500 with
                   | (t1,ctrl1) ->
                       let uu____8515 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8515
                         (fun uu____8542  ->
                            match uu____8542 with
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
              let uu____8626 =
                let uu____8633 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8633
                  (fun uu____8642  ->
                     let uu____8643 = ctrl t1  in
                     bind uu____8643
                       (fun res  ->
                          let uu____8666 = trivial ()  in
                          bind uu____8666 (fun uu____8674  -> ret res)))
                 in
              bind uu____8626
                (fun uu____8690  ->
                   match uu____8690 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8714 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___417_8723 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___417_8723.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___417_8723.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___417_8723.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___417_8723.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___417_8723.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___417_8723.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___417_8723.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___417_8723.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___417_8723.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___417_8723.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___417_8723.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___417_8723.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___417_8723.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___417_8723.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___417_8723.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___417_8723.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___417_8723.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___417_8723.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___417_8723.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___417_8723.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___417_8723.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___417_8723.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___417_8723.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___417_8723.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___417_8723.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___417_8723.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___417_8723.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___417_8723.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___417_8723.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___417_8723.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___417_8723.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___417_8723.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___417_8723.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___417_8723.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___417_8723.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___417_8723.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___417_8723.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___417_8723.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___417_8723.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___417_8723.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___417_8723.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8714 with
                          | (t2,lcomp,g) ->
                              let uu____8733 =
                                (let uu____8736 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8736) ||
                                  (let uu____8738 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8738)
                                 in
                              if uu____8733
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8751 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8751
                                   (fun uu____8771  ->
                                      match uu____8771 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8788  ->
                                                let uu____8789 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8790 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8789 uu____8790);
                                           (let uu____8791 =
                                              let uu____8794 =
                                                let uu____8795 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8795 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8794 opts
                                               in
                                            bind uu____8791
                                              (fun uu____8802  ->
                                                 let uu____8803 =
                                                   bind rewriter
                                                     (fun uu____8817  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8823  ->
                                                             let uu____8824 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8825 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8824
                                                               uu____8825);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8803)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8866 =
        bind get
          (fun ps  ->
             let uu____8876 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8876 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8913  ->
                       let uu____8914 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8914);
                  bind dismiss_all
                    (fun uu____8917  ->
                       let uu____8918 =
                         let uu____8925 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8925
                           keepGoing gt1
                          in
                       bind uu____8918
                         (fun uu____8937  ->
                            match uu____8937 with
                            | (gt',uu____8945) ->
                                (log ps
                                   (fun uu____8949  ->
                                      let uu____8950 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8950);
                                 (let uu____8951 = push_goals gs  in
                                  bind uu____8951
                                    (fun uu____8956  ->
                                       let uu____8957 =
                                         let uu____8960 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8960]  in
                                       add_goals uu____8957)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8866
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8983 =
        bind get
          (fun ps  ->
             let uu____8993 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8993 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9030  ->
                       let uu____9031 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____9031);
                  bind dismiss_all
                    (fun uu____9034  ->
                       let uu____9035 =
                         let uu____9038 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____9038 gt1
                          in
                       bind uu____9035
                         (fun gt'  ->
                            log ps
                              (fun uu____9046  ->
                                 let uu____9047 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____9047);
                            (let uu____9048 = push_goals gs  in
                             bind uu____9048
                               (fun uu____9053  ->
                                  let uu____9054 =
                                    let uu____9057 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____9057]  in
                                  add_goals uu____9054))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8983
  
let (trefl : unit -> unit tac) =
  fun uu____9068  ->
    let uu____9071 =
      let uu____9074 = cur_goal ()  in
      bind uu____9074
        (fun g  ->
           let uu____9092 =
             let uu____9097 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____9097  in
           match uu____9092 with
           | FStar_Pervasives_Native.Some t ->
               let uu____9105 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____9105 with
                | (hd1,args) ->
                    let uu____9144 =
                      let uu____9157 =
                        let uu____9158 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9158.FStar_Syntax_Syntax.n  in
                      (uu____9157, args)  in
                    (match uu____9144 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9172::(l,uu____9174)::(r,uu____9176)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9223 =
                           let uu____9226 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9226 l r  in
                         bind uu____9223
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9233 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9233 l
                                    in
                                 let r1 =
                                   let uu____9235 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9235 r
                                    in
                                 let uu____9236 =
                                   let uu____9239 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9239 l1 r1  in
                                 bind uu____9236
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9245 =
                                           let uu____9246 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9246 l1  in
                                         let uu____9247 =
                                           let uu____9248 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9248 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9245 uu____9247))))
                     | (hd2,uu____9250) ->
                         let uu____9267 =
                           let uu____9268 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9268 t  in
                         fail1 "trefl: not an equality (%s)" uu____9267))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____9071
  
let (dup : unit -> unit tac) =
  fun uu____9281  ->
    let uu____9284 = cur_goal ()  in
    bind uu____9284
      (fun g  ->
         let uu____9290 =
           let uu____9297 = FStar_Tactics_Types.goal_env g  in
           let uu____9298 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9297 uu____9298  in
         bind uu____9290
           (fun uu____9307  ->
              match uu____9307 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___418_9317 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___418_9317.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___418_9317.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___418_9317.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9320  ->
                       let uu____9321 =
                         let uu____9324 = FStar_Tactics_Types.goal_env g  in
                         let uu____9325 =
                           let uu____9326 =
                             let uu____9327 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9328 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9327
                               uu____9328
                              in
                           let uu____9329 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9330 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9326 uu____9329 u
                             uu____9330
                            in
                         add_irrelevant_goal "dup equation" uu____9324
                           uu____9325 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9321
                         (fun uu____9333  ->
                            let uu____9334 = add_goals [g']  in
                            bind uu____9334 (fun uu____9338  -> ret ())))))
  
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
              let uu____9461 = f x y  in
              if uu____9461 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9481 -> (acc, l11, l21)  in
        let uu____9496 = aux [] l1 l2  in
        match uu____9496 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9601 = get_phi g1  in
      match uu____9601 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9607 = get_phi g2  in
          (match uu____9607 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9619 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9619 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9650 =
                        FStar_TypeChecker_Env.binders_of_bindings r1  in
                      close_forall_no_univs1 uu____9650 phi1  in
                    let t2 =
                      let uu____9660 =
                        FStar_TypeChecker_Env.binders_of_bindings r2  in
                      close_forall_no_univs1 uu____9660 phi2  in
                    let uu____9669 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9669
                      (fun uu____9674  ->
                         let uu____9675 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9675
                           (fun uu____9682  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___419_9687 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9688 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___419_9687.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___419_9687.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___419_9687.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___419_9687.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9688;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___419_9687.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___419_9687.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___419_9687.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___419_9687.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___419_9687.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___419_9687.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___419_9687.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___419_9687.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___419_9687.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___419_9687.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___419_9687.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___419_9687.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___419_9687.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___419_9687.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___419_9687.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___419_9687.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___419_9687.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___419_9687.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___419_9687.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___419_9687.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___419_9687.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___419_9687.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___419_9687.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___419_9687.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___419_9687.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___419_9687.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___419_9687.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___419_9687.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___419_9687.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___419_9687.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___419_9687.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___419_9687.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___419_9687.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___419_9687.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___419_9687.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___419_9687.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9691 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9691
                                (fun goal  ->
                                   mlog
                                     (fun uu____9700  ->
                                        let uu____9701 =
                                          goal_to_string_verbose g1  in
                                        let uu____9702 =
                                          goal_to_string_verbose g2  in
                                        let uu____9703 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9701 uu____9702 uu____9703)
                                     (fun uu____9705  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9712  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9728 =
               set
                 (let uu___420_9733 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___420_9733.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___420_9733.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___420_9733.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___420_9733.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___420_9733.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___420_9733.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___420_9733.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___420_9733.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___420_9733.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___420_9733.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___420_9733.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___420_9733.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9728
               (fun uu____9736  ->
                  let uu____9737 = join_goals g1 g2  in
                  bind uu____9737 (fun g12  -> add_goals [g12]))
         | uu____9742 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9762 =
      let uu____9769 = cur_goal ()  in
      bind uu____9769
        (fun g  ->
           let uu____9779 =
             let uu____9788 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9788 t  in
           bind uu____9779
             (fun uu____9816  ->
                match uu____9816 with
                | (t1,typ,guard) ->
                    let uu____9832 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9832 with
                     | (hd1,args) ->
                         let uu____9881 =
                           let uu____9896 =
                             let uu____9897 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9897.FStar_Syntax_Syntax.n  in
                           (uu____9896, args)  in
                         (match uu____9881 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9918)::(q,uu____9920)::[]) when
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
                                let uu____9974 =
                                  let uu____9975 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9975
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9974
                                 in
                              let g2 =
                                let uu____9977 =
                                  let uu____9978 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9978
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9977
                                 in
                              bind __dismiss
                                (fun uu____9985  ->
                                   let uu____9986 = add_goals [g1; g2]  in
                                   bind uu____9986
                                     (fun uu____9995  ->
                                        let uu____9996 =
                                          let uu____10001 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____10002 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____10001, uu____10002)  in
                                        ret uu____9996))
                          | uu____10007 ->
                              let uu____10022 =
                                let uu____10023 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____10023 typ  in
                              fail1 "Not a disjunction: %s" uu____10022))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9762
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____10053 =
      let uu____10056 = cur_goal ()  in
      bind uu____10056
        (fun g  ->
           FStar_Options.push ();
           (let uu____10069 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____10069);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___421_10076 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___421_10076.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___421_10076.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___421_10076.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____10053
  
let (top_env : unit -> env tac) =
  fun uu____10088  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10101  ->
    let uu____10104 = cur_goal ()  in
    bind uu____10104
      (fun g  ->
         let uu____10110 =
           (FStar_Options.lax ()) ||
             (let uu____10112 = FStar_Tactics_Types.goal_env g  in
              uu____10112.FStar_TypeChecker_Env.lax)
            in
         ret uu____10110)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10127 =
        mlog
          (fun uu____10132  ->
             let uu____10133 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10133)
          (fun uu____10136  ->
             let uu____10137 = cur_goal ()  in
             bind uu____10137
               (fun goal  ->
                  let env =
                    let uu____10145 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10145 ty  in
                  let uu____10146 = __tc_ghost env tm  in
                  bind uu____10146
                    (fun uu____10165  ->
                       match uu____10165 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10179  ->
                                let uu____10180 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10180)
                             (fun uu____10182  ->
                                mlog
                                  (fun uu____10185  ->
                                     let uu____10186 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10186)
                                  (fun uu____10189  ->
                                     let uu____10190 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10190
                                       (fun uu____10194  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10127
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10217 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10223 =
              let uu____10230 =
                let uu____10231 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10231
                 in
              new_uvar "uvar_env.2" env uu____10230  in
            bind uu____10223
              (fun uu____10247  ->
                 match uu____10247 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10217
        (fun typ  ->
           let uu____10259 = new_uvar "uvar_env" env typ  in
           bind uu____10259
             (fun uu____10273  ->
                match uu____10273 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10291 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10310 -> g.FStar_Tactics_Types.opts
             | uu____10313 -> FStar_Options.peek ()  in
           let uu____10316 = FStar_Syntax_Util.head_and_args t  in
           match uu____10316 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10336);
                FStar_Syntax_Syntax.pos = uu____10337;
                FStar_Syntax_Syntax.vars = uu____10338;_},uu____10339)
               ->
               let env1 =
                 let uu___422_10381 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___422_10381.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___422_10381.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___422_10381.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___422_10381.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___422_10381.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___422_10381.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___422_10381.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___422_10381.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___422_10381.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___422_10381.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___422_10381.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___422_10381.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___422_10381.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___422_10381.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___422_10381.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___422_10381.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___422_10381.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___422_10381.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___422_10381.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___422_10381.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___422_10381.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___422_10381.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___422_10381.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___422_10381.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___422_10381.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___422_10381.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___422_10381.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___422_10381.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___422_10381.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___422_10381.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___422_10381.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___422_10381.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___422_10381.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___422_10381.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___422_10381.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___422_10381.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___422_10381.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___422_10381.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___422_10381.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___422_10381.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___422_10381.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10383 =
                 let uu____10386 = bnorm_goal g  in [uu____10386]  in
               add_goals uu____10383
           | uu____10387 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10291
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10436 = if b then t2 else ret false  in
             bind uu____10436 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10447 = trytac comp  in
      bind uu____10447
        (fun uu___351_10455  ->
           match uu___351_10455 with
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
        let uu____10481 =
          bind get
            (fun ps  ->
               let uu____10487 = __tc e t1  in
               bind uu____10487
                 (fun uu____10507  ->
                    match uu____10507 with
                    | (t11,ty1,g1) ->
                        let uu____10519 = __tc e t2  in
                        bind uu____10519
                          (fun uu____10539  ->
                             match uu____10539 with
                             | (t21,ty2,g2) ->
                                 let uu____10551 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10551
                                   (fun uu____10556  ->
                                      let uu____10557 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10557
                                        (fun uu____10563  ->
                                           let uu____10564 =
                                             do_unify e ty1 ty2  in
                                           let uu____10567 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10564 uu____10567)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10481
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10600  ->
             let uu____10601 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10601
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
        (fun uu____10622  ->
           let uu____10623 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10623)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10633 =
      mlog
        (fun uu____10638  ->
           let uu____10639 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10639)
        (fun uu____10642  ->
           let uu____10643 = cur_goal ()  in
           bind uu____10643
             (fun g  ->
                let uu____10649 =
                  let uu____10658 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10658 ty  in
                bind uu____10649
                  (fun uu____10670  ->
                     match uu____10670 with
                     | (ty1,uu____10680,guard) ->
                         let uu____10682 =
                           let uu____10685 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10685 guard  in
                         bind uu____10682
                           (fun uu____10688  ->
                              let uu____10689 =
                                let uu____10692 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10693 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10692 uu____10693 ty1  in
                              bind uu____10689
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10699 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10699
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10705 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10706 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10705
                                          uu____10706
                                         in
                                      let nty =
                                        let uu____10708 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10708 ty1  in
                                      let uu____10709 =
                                        let uu____10712 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10712 ng nty  in
                                      bind uu____10709
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10718 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10718
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10633
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10781 =
      let uu____10790 = cur_goal ()  in
      bind uu____10790
        (fun g  ->
           let uu____10802 =
             let uu____10811 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10811 s_tm  in
           bind uu____10802
             (fun uu____10829  ->
                match uu____10829 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10847 =
                      let uu____10850 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10850 guard  in
                    bind uu____10847
                      (fun uu____10862  ->
                         let uu____10863 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10863 with
                         | (h,args) ->
                             let uu____10908 =
                               let uu____10915 =
                                 let uu____10916 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10916.FStar_Syntax_Syntax.n  in
                               match uu____10915 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10931;
                                      FStar_Syntax_Syntax.vars = uu____10932;_},us)
                                   -> ret (fv, us)
                               | uu____10942 -> fail "type is not an fv"  in
                             bind uu____10908
                               (fun uu____10962  ->
                                  match uu____10962 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10978 =
                                        let uu____10981 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10981 t_lid
                                         in
                                      (match uu____10978 with
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
                                                  (fun uu____11030  ->
                                                     let uu____11031 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____11031 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____11046 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____11074
                                                                  =
                                                                  let uu____11077
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____11077
                                                                    c_lid
                                                                   in
                                                                match uu____11074
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
                                                                    uu____11147
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
                                                                    let uu____11152
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11152
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11175
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11175
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11218
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11218
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11291
                                                                    =
                                                                    let uu____11292
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11292
                                                                     in
                                                                    failwhen
                                                                    uu____11291
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11309
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
                                                                    uu___352_11325
                                                                    =
                                                                    match uu___352_11325
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11328)
                                                                    -> true
                                                                    | 
                                                                    uu____11329
                                                                    -> false
                                                                     in
                                                                    let uu____11332
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11332
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
                                                                    uu____11465
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
                                                                    uu____11527
                                                                     ->
                                                                    match uu____11527
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11547),
                                                                    (t,uu____11549))
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
                                                                    uu____11617
                                                                     ->
                                                                    match uu____11617
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11643),
                                                                    (t,uu____11645))
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
                                                                    uu____11700
                                                                     ->
                                                                    match uu____11700
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
                                                                    let uu____11750
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___423_11767
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___423_11767.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____11750
                                                                    with
                                                                    | 
                                                                    (uu____11780,uu____11781,uu____11782,pat_t,uu____11784,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11791
                                                                    =
                                                                    let uu____11792
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11792
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11791
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11796
                                                                    =
                                                                    let uu____11805
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11805]
                                                                     in
                                                                    let uu____11824
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11796
                                                                    uu____11824
                                                                     in
                                                                    let nty =
                                                                    let uu____11830
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11830
                                                                     in
                                                                    let uu____11833
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11833
                                                                    (fun
                                                                    uu____11862
                                                                     ->
                                                                    match uu____11862
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
                                                                    let uu____11888
                                                                    =
                                                                    let uu____11899
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11899]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11888
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11935
                                                                    =
                                                                    let uu____11946
                                                                    =
                                                                    let uu____11951
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11951)
                                                                     in
                                                                    (g', br,
                                                                    uu____11946)
                                                                     in
                                                                    ret
                                                                    uu____11935))))))
                                                                    | 
                                                                    uu____11972
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____11046
                                                           (fun goal_brs  ->
                                                              let uu____12021
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____12021
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
                                                                  let uu____12094
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12094
                                                                    (
                                                                    fun
                                                                    uu____12105
                                                                     ->
                                                                    let uu____12106
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12106
                                                                    (fun
                                                                    uu____12116
                                                                     ->
                                                                    ret infos))))
                                            | uu____12123 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10781
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12168::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12196 = init xs  in x :: uu____12196
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12208 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12217) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12282 = last args  in
          (match uu____12282 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12312 =
                 let uu____12313 =
                   let uu____12318 =
                     let uu____12319 =
                       let uu____12324 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12324  in
                     uu____12319 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12318, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12313  in
               FStar_All.pipe_left ret uu____12312)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12337,uu____12338) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12390 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12390 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12431 =
                      let uu____12432 =
                        let uu____12437 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12437)  in
                      FStar_Reflection_Data.Tv_Abs uu____12432  in
                    FStar_All.pipe_left ret uu____12431))
      | FStar_Syntax_Syntax.Tm_type uu____12440 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12464 ->
          let uu____12479 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12479 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12509 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12509 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12562 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12574 =
            let uu____12575 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12575  in
          FStar_All.pipe_left ret uu____12574
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12596 =
            let uu____12597 =
              let uu____12602 =
                let uu____12603 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12603  in
              (uu____12602, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12597  in
          FStar_All.pipe_left ret uu____12596
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12637 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12642 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12642 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12695 ->
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
             | FStar_Util.Inr uu____12729 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12733 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12733 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12753 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12757 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12811 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12811
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12830 =
                  let uu____12837 =
                    FStar_List.map
                      (fun uu____12849  ->
                         match uu____12849 with
                         | (p1,uu____12857) -> inspect_pat p1) ps
                     in
                  (fv, uu____12837)  in
                FStar_Reflection_Data.Pat_Cons uu____12830
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
              (fun uu___353_12951  ->
                 match uu___353_12951 with
                 | (pat,uu____12973,t5) ->
                     let uu____12991 = inspect_pat pat  in (uu____12991, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____13000 ->
          ((let uu____13002 =
              let uu____13007 =
                let uu____13008 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____13009 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____13008 uu____13009
                 in
              (FStar_Errors.Warning_CantInspect, uu____13007)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____13002);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12208
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____13022 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____13022
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____13026 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____13026
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____13030 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____13030
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____13037 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____13037
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____13062 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____13062
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____13079 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____13079
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13098 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13098
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13102 =
          let uu____13103 =
            let uu____13110 =
              let uu____13111 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13111  in
            FStar_Syntax_Syntax.mk uu____13110  in
          uu____13103 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13102
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13119 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13119
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13128 =
          let uu____13129 =
            let uu____13136 =
              let uu____13137 =
                let uu____13150 =
                  let uu____13153 =
                    let uu____13154 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13154]  in
                  FStar_Syntax_Subst.close uu____13153 t2  in
                ((false, [lb]), uu____13150)  in
              FStar_Syntax_Syntax.Tm_let uu____13137  in
            FStar_Syntax_Syntax.mk uu____13136  in
          uu____13129 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13128
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13194 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13194 with
         | (lbs,body) ->
             let uu____13209 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13209)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13243 =
                let uu____13244 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13244  in
              FStar_All.pipe_left wrap uu____13243
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13251 =
                let uu____13252 =
                  let uu____13265 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13281 = pack_pat p1  in
                         (uu____13281, false)) ps
                     in
                  (fv, uu____13265)  in
                FStar_Syntax_Syntax.Pat_cons uu____13252  in
              FStar_All.pipe_left wrap uu____13251
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
            (fun uu___354_13327  ->
               match uu___354_13327 with
               | (pat,t1) ->
                   let uu____13344 = pack_pat pat  in
                   (uu____13344, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13392 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13392
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13420 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13420
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13466 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13466
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13505 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13505
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13522 =
        bind get
          (fun ps  ->
             let uu____13528 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13528 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13522
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13557 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___424_13564 = ps  in
                 let uu____13565 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___424_13564.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___424_13564.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___424_13564.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___424_13564.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___424_13564.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___424_13564.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___424_13564.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___424_13564.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___424_13564.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___424_13564.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___424_13564.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___424_13564.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13565
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13557
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13590 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13590 with
      | (u,ctx_uvars,g_u) ->
          let uu____13622 = FStar_List.hd ctx_uvars  in
          (match uu____13622 with
           | (ctx_uvar,uu____13636) ->
               let g =
                 let uu____13638 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13638 false
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
        let uu____13658 = goal_of_goal_ty env typ  in
        match uu____13658 with
        | (g,g_u) ->
            let ps =
              let uu____13670 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13671 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13670;
                FStar_Tactics_Types.local_state = uu____13671
              }  in
            let uu____13678 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13678)
  