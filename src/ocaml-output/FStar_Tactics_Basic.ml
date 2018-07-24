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
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
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
  fun uu____2157  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___377_2175 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___377_2175.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___377_2175.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___377_2175.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___377_2175.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___377_2175.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___377_2175.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___377_2175.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___377_2175.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___377_2175.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___377_2175.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___377_2175.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___377_2175.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2199 = get_guard_policy ()  in
      bind uu____2199
        (fun old_pol  ->
           let uu____2205 = set_guard_policy pol  in
           bind uu____2205
             (fun uu____2209  ->
                bind t
                  (fun r  ->
                     let uu____2213 = set_guard_policy old_pol  in
                     bind uu____2213 (fun uu____2217  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2220 = let uu____2225 = cur_goal ()  in trytac uu____2225  in
  bind uu____2220
    (fun uu___347_2232  ->
       match uu___347_2232 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2238 = FStar_Options.peek ()  in ret uu____2238)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2260  ->
             let uu____2261 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2261)
          (fun uu____2264  ->
             let uu____2265 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2265
               (fun uu____2269  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2273 =
                         let uu____2274 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2274.FStar_TypeChecker_Env.guard_f  in
                       match uu____2273 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2278 = istrivial e f  in
                           if uu____2278
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2288 =
                                          let uu____2293 =
                                            let uu____2294 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2294
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2293)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2288);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2297  ->
                                           let uu____2298 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2298)
                                        (fun uu____2301  ->
                                           let uu____2302 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2302
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___378_2309 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___378_2309.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___378_2309.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___378_2309.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2312  ->
                                           let uu____2313 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2313)
                                        (fun uu____2316  ->
                                           let uu____2317 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2317
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___379_2324 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___379_2324.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___379_2324.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___379_2324.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2327  ->
                                           let uu____2328 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2328)
                                        (fun uu____2330  ->
                                           try
                                             (fun uu___381_2335  ->
                                                match () with
                                                | () ->
                                                    let uu____2338 =
                                                      let uu____2339 =
                                                        let uu____2340 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2340
                                                         in
                                                      Prims.op_Negation
                                                        uu____2339
                                                       in
                                                    if uu____2338
                                                    then
                                                      mlog
                                                        (fun uu____2345  ->
                                                           let uu____2346 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2346)
                                                        (fun uu____2348  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___380_2351 ->
                                               mlog
                                                 (fun uu____2356  ->
                                                    let uu____2357 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2357)
                                                 (fun uu____2359  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2369 =
      let uu____2372 = cur_goal ()  in
      bind uu____2372
        (fun goal  ->
           let uu____2378 =
             let uu____2387 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2387 t  in
           bind uu____2378
             (fun uu____2398  ->
                match uu____2398 with
                | (uu____2407,typ,uu____2409) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2369
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2438 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2438 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2449  ->
    let uu____2452 = cur_goal ()  in
    bind uu____2452
      (fun goal  ->
         let uu____2458 =
           let uu____2459 = FStar_Tactics_Types.goal_env goal  in
           let uu____2460 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2459 uu____2460  in
         if uu____2458
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2464 =
              let uu____2465 = FStar_Tactics_Types.goal_env goal  in
              let uu____2466 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2465 uu____2466  in
            fail1 "Not a trivial goal: %s" uu____2464))
  
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
          let uu____2495 =
            let uu____2496 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2496.FStar_TypeChecker_Env.guard_f  in
          match uu____2495 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2504 = istrivial e f  in
              if uu____2504
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2512 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2512
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___382_2522 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___382_2522.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___382_2522.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___382_2522.FStar_Tactics_Types.opts);
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
             let uu____2571 =
               try
                 (fun uu___387_2594  ->
                    match () with
                    | () ->
                        let uu____2605 =
                          let uu____2614 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2614
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2605) ()
               with | uu___386_2624 -> fail "divide: not enough goals"  in
             bind uu____2571
               (fun uu____2660  ->
                  match uu____2660 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___383_2686 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___383_2686.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___383_2686.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___383_2686.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___383_2686.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___383_2686.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___383_2686.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___383_2686.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___383_2686.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___383_2686.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___383_2686.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___383_2686.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2687 = set lp  in
                      bind uu____2687
                        (fun uu____2695  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___384_2711 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___384_2711.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___384_2711.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___384_2711.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___384_2711.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___384_2711.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___384_2711.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___384_2711.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___384_2711.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___384_2711.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___384_2711.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___384_2711.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2712 = set rp  in
                                     bind uu____2712
                                       (fun uu____2720  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___385_2736 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___385_2736.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___385_2736.FStar_Tactics_Types.local_state)
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
                  let uu____2968 = new_uvar "intro" env' typ'  in
                  bind uu____2968
                    (fun uu____2984  ->
                       match uu____2984 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3008 = set_solution goal sol  in
                           bind uu____3008
                             (fun uu____3014  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3016 =
                                  let uu____3019 = bnorm_goal g  in
                                  replace_cur uu____3019  in
                                bind uu____3016 (fun uu____3021  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3026 =
                 let uu____3027 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3028 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3027 uu____3028  in
               fail1 "goal is not an arrow (%s)" uu____3026)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2920
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3043  ->
    let uu____3050 = cur_goal ()  in
    bind uu____3050
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3067 =
            let uu____3074 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3074  in
          match uu____3067 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3087 =
                let uu____3088 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3088  in
              if uu____3087
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3101 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3101
                    in
                 let bs =
                   let uu____3111 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3111; b]  in
                 let env' =
                   let uu____3137 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3137 bs  in
                 let uu____3138 =
                   let uu____3145 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3145  in
                 bind uu____3138
                   (fun uu____3164  ->
                      match uu____3164 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3178 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3181 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3178
                              FStar_Parser_Const.effect_Tot_lid uu____3181 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3199 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3199 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3221 =
                                   let uu____3222 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3222.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3221
                                  in
                               let uu____3235 = set_solution goal tm  in
                               bind uu____3235
                                 (fun uu____3244  ->
                                    let uu____3245 =
                                      let uu____3248 =
                                        bnorm_goal
                                          (let uu___388_3251 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___388_3251.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___388_3251.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___388_3251.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3248  in
                                    bind uu____3245
                                      (fun uu____3258  ->
                                         let uu____3259 =
                                           let uu____3264 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3264, b)  in
                                         ret uu____3259)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3273 =
                let uu____3274 = FStar_Tactics_Types.goal_env goal  in
                let uu____3275 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3274 uu____3275  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3273))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3293 = cur_goal ()  in
    bind uu____3293
      (fun goal  ->
         mlog
           (fun uu____3300  ->
              let uu____3301 =
                let uu____3302 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3302  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3301)
           (fun uu____3307  ->
              let steps =
                let uu____3311 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3311
                 in
              let t =
                let uu____3315 = FStar_Tactics_Types.goal_env goal  in
                let uu____3316 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3315 uu____3316  in
              let uu____3317 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3317))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3341 =
          mlog
            (fun uu____3346  ->
               let uu____3347 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3347)
            (fun uu____3349  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3355 -> g.FStar_Tactics_Types.opts
                      | uu____3358 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3363  ->
                         let uu____3364 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3364)
                      (fun uu____3367  ->
                         let uu____3368 = __tc e t  in
                         bind uu____3368
                           (fun uu____3389  ->
                              match uu____3389 with
                              | (t1,uu____3399,uu____3400) ->
                                  let steps =
                                    let uu____3404 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3404
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3341
  
let (refine_intro : unit -> unit tac) =
  fun uu____3418  ->
    let uu____3421 =
      let uu____3424 = cur_goal ()  in
      bind uu____3424
        (fun g  ->
           let uu____3431 =
             let uu____3442 = FStar_Tactics_Types.goal_env g  in
             let uu____3443 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3442 uu____3443
              in
           match uu____3431 with
           | (uu____3446,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3471 =
                 let uu____3476 =
                   let uu____3481 =
                     let uu____3482 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3482]  in
                   FStar_Syntax_Subst.open_term uu____3481 phi  in
                 match uu____3476 with
                 | (bvs,phi1) ->
                     let uu____3507 =
                       let uu____3508 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3508  in
                     (uu____3507, phi1)
                  in
               (match uu____3471 with
                | (bv1,phi1) ->
                    let uu____3527 =
                      let uu____3530 = FStar_Tactics_Types.goal_env g  in
                      let uu____3531 =
                        let uu____3532 =
                          let uu____3535 =
                            let uu____3536 =
                              let uu____3543 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3543)  in
                            FStar_Syntax_Syntax.NT uu____3536  in
                          [uu____3535]  in
                        FStar_Syntax_Subst.subst uu____3532 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3530
                        uu____3531 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3527
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3551  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3421
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3570 = cur_goal ()  in
      bind uu____3570
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3578 = FStar_Tactics_Types.goal_env goal  in
               let uu____3579 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3578 uu____3579
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3581 = __tc env t  in
           bind uu____3581
             (fun uu____3600  ->
                match uu____3600 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3615  ->
                         let uu____3616 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3617 =
                           let uu____3618 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3618
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3616 uu____3617)
                      (fun uu____3621  ->
                         let uu____3622 =
                           let uu____3625 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3625 guard  in
                         bind uu____3622
                           (fun uu____3627  ->
                              mlog
                                (fun uu____3631  ->
                                   let uu____3632 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3633 =
                                     let uu____3634 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3634
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3632 uu____3633)
                                (fun uu____3637  ->
                                   let uu____3638 =
                                     let uu____3641 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3642 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3641 typ uu____3642  in
                                   bind uu____3638
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3648 =
                                             let uu____3649 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3649 t1  in
                                           let uu____3650 =
                                             let uu____3651 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3651 typ  in
                                           let uu____3652 =
                                             let uu____3653 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3654 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3653 uu____3654  in
                                           let uu____3655 =
                                             let uu____3656 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3657 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3656 uu____3657  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3648 uu____3650 uu____3652
                                             uu____3655)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3677 =
          mlog
            (fun uu____3682  ->
               let uu____3683 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3683)
            (fun uu____3686  ->
               let uu____3687 =
                 let uu____3694 = __exact_now set_expected_typ1 tm  in
                 catch uu____3694  in
               bind uu____3687
                 (fun uu___349_3703  ->
                    match uu___349_3703 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3714  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3717  ->
                             let uu____3718 =
                               let uu____3725 =
                                 let uu____3728 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3728
                                   (fun uu____3733  ->
                                      let uu____3734 = refine_intro ()  in
                                      bind uu____3734
                                        (fun uu____3738  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3725  in
                             bind uu____3718
                               (fun uu___348_3745  ->
                                  match uu___348_3745 with
                                  | FStar_Util.Inr r -> ret ()
                                  | FStar_Util.Inl uu____3753 -> fail e))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3677
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3803 = f x  in
          bind uu____3803
            (fun y  ->
               let uu____3811 = mapM f xs  in
               bind uu____3811 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3882 = do_unify e ty1 ty2  in
          bind uu____3882
            (fun uu___350_3894  ->
               if uu___350_3894
               then ret acc
               else
                 (let uu____3913 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3913 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3934 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3935 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3934
                        uu____3935
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3950 =
                        let uu____3951 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3951  in
                      if uu____3950
                      then fail "Codomain is effectful"
                      else
                        (let uu____3971 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3971
                           (fun uu____3997  ->
                              match uu____3997 with
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
      let uu____4083 =
        mlog
          (fun uu____4088  ->
             let uu____4089 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4089)
          (fun uu____4092  ->
             let uu____4093 = cur_goal ()  in
             bind uu____4093
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4101 = __tc e tm  in
                  bind uu____4101
                    (fun uu____4122  ->
                       match uu____4122 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4135 =
                             let uu____4146 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4146  in
                           bind uu____4135
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4189  ->
                                       fun w  ->
                                         match uu____4189 with
                                         | (uvt,q,uu____4207) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4239 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4256  ->
                                       fun s  ->
                                         match uu____4256 with
                                         | (uu____4268,uu____4269,uv) ->
                                             let uu____4271 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4271) uvs uu____4239
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4280 = solve' goal w  in
                                bind uu____4280
                                  (fun uu____4285  ->
                                     let uu____4286 =
                                       mapM
                                         (fun uu____4303  ->
                                            match uu____4303 with
                                            | (uvt,q,uv) ->
                                                let uu____4315 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4315 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4320 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4321 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4321
                                                     then ret ()
                                                     else
                                                       (let uu____4325 =
                                                          let uu____4328 =
                                                            bnorm_goal
                                                              (let uu___389_4331
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___389_4331.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___389_4331.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4328]  in
                                                        add_goals uu____4325)))
                                         uvs
                                        in
                                     bind uu____4286
                                       (fun uu____4335  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4083
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4360 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4360
    then
      let uu____4367 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4382 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4435 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4367 with
      | (pre,post) ->
          let post1 =
            let uu____4467 =
              let uu____4478 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4478]  in
            FStar_Syntax_Util.mk_app post uu____4467  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4508 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4508
       then
         let uu____4515 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4515
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4548 =
      let uu____4551 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4558  ->
                  let uu____4559 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4559)
               (fun uu____4563  ->
                  let is_unit_t t =
                    let uu____4570 =
                      let uu____4571 = FStar_Syntax_Subst.compress t  in
                      uu____4571.FStar_Syntax_Syntax.n  in
                    match uu____4570 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4575 -> false  in
                  let uu____4576 = cur_goal ()  in
                  bind uu____4576
                    (fun goal  ->
                       let uu____4582 =
                         let uu____4591 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4591 tm  in
                       bind uu____4582
                         (fun uu____4606  ->
                            match uu____4606 with
                            | (tm1,t,guard) ->
                                let uu____4618 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4618 with
                                 | (bs,comp) ->
                                     let uu____4651 = lemma_or_sq comp  in
                                     (match uu____4651 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4670 =
                                            FStar_List.fold_left
                                              (fun uu____4718  ->
                                                 fun uu____4719  ->
                                                   match (uu____4718,
                                                           uu____4719)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4832 =
                                                         is_unit_t b_t  in
                                                       if uu____4832
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4870 =
                                                            let uu____4883 =
                                                              let uu____4884
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____4884.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____4887 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____4883
                                                              uu____4887 b_t
                                                             in
                                                          match uu____4870
                                                          with
                                                          | (u,uu____4905,g_u)
                                                              ->
                                                              let uu____4919
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4919,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4670 with
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
                                               let uu____4998 =
                                                 let uu____5001 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5002 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5003 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5001
                                                   uu____5002 uu____5003
                                                  in
                                               bind uu____4998
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5011 =
                                                        let uu____5012 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5012 tm1
                                                         in
                                                      let uu____5013 =
                                                        let uu____5014 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5015 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5014
                                                          uu____5015
                                                         in
                                                      let uu____5016 =
                                                        let uu____5017 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5018 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5017
                                                          uu____5018
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5011 uu____5013
                                                        uu____5016
                                                    else
                                                      (let uu____5020 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5020
                                                         (fun uu____5025  ->
                                                            let uu____5026 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5026
                                                              (fun uu____5034
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5059
                                                                    =
                                                                    let uu____5062
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5062
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5059
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
                                                                    let uu____5097
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5097)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5113
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5113
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5131)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5157)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5174
                                                                    -> false)
                                                                    in
                                                                 let uu____5175
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
                                                                    let uu____5205
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5205
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5227)
                                                                    ->
                                                                    let uu____5252
                                                                    =
                                                                    let uu____5253
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5253.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5252
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5261)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___390_5281
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___390_5281.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___390_5281.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___390_5281.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5284
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5290
                                                                     ->
                                                                    let uu____5291
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5292
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5291
                                                                    uu____5292)
                                                                    (fun
                                                                    uu____5297
                                                                     ->
                                                                    let env =
                                                                    let uu___391_5299
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___391_5299.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5301
                                                                    =
                                                                    let uu____5304
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5305
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5306
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5305
                                                                    uu____5306
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5308
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5304
                                                                    uu____5308
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5301
                                                                    (fun
                                                                    uu____5312
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5175
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
                                                                    let uu____5374
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5374
                                                                    then
                                                                    let uu____5377
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5377
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
                                                                    let uu____5391
                                                                    =
                                                                    let uu____5392
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5392
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5391)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5393
                                                                    =
                                                                    let uu____5396
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5396
                                                                    guard  in
                                                                    bind
                                                                    uu____5393
                                                                    (fun
                                                                    uu____5399
                                                                     ->
                                                                    let uu____5400
                                                                    =
                                                                    let uu____5403
                                                                    =
                                                                    let uu____5404
                                                                    =
                                                                    let uu____5405
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5406
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5405
                                                                    uu____5406
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5404
                                                                     in
                                                                    if
                                                                    uu____5403
                                                                    then
                                                                    let uu____5409
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5409
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5400
                                                                    (fun
                                                                    uu____5412
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4551  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4548
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5434 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5434 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5444::(e1,uu____5446)::(e2,uu____5448)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5509 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5533 = destruct_eq' typ  in
    match uu____5533 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5563 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5563 with
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
        let uu____5625 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5625 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5673 = aux e'  in
               FStar_Util.map_opt uu____5673
                 (fun uu____5697  ->
                    match uu____5697 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5718 = aux e  in
      FStar_Util.map_opt uu____5718
        (fun uu____5742  ->
           match uu____5742 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5809 =
            let uu____5818 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5818  in
          FStar_Util.map_opt uu____5809
            (fun uu____5833  ->
               match uu____5833 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___392_5852 = bv  in
                     let uu____5853 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___392_5852.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___392_5852.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5853
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___393_5861 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5862 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5871 =
                       let uu____5874 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5874  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___393_5861.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5862;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5871;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___393_5861.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___393_5861.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___393_5861.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___394_5875 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___394_5875.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___394_5875.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___394_5875.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5885 =
      let uu____5888 = cur_goal ()  in
      bind uu____5888
        (fun goal  ->
           let uu____5896 = h  in
           match uu____5896 with
           | (bv,uu____5900) ->
               mlog
                 (fun uu____5908  ->
                    let uu____5909 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5910 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5909
                      uu____5910)
                 (fun uu____5913  ->
                    let uu____5914 =
                      let uu____5923 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5923  in
                    match uu____5914 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5944 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5944 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5959 =
                               let uu____5960 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5960.FStar_Syntax_Syntax.n  in
                             (match uu____5959 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___395_5977 = bv1  in
                                    let uu____5978 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___395_5977.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___395_5977.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5978
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___396_5986 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5987 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5996 =
                                      let uu____5999 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____5999
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___396_5986.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5987;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5996;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___396_5986.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___396_5986.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___396_5986.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___397_6002 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___397_6002.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___397_6002.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___397_6002.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6003 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6004 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5885
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6029 =
        let uu____6032 = cur_goal ()  in
        bind uu____6032
          (fun goal  ->
             let uu____6043 = b  in
             match uu____6043 with
             | (bv,uu____6047) ->
                 let bv' =
                   let uu____6053 =
                     let uu___398_6054 = bv  in
                     let uu____6055 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6055;
                       FStar_Syntax_Syntax.index =
                         (uu___398_6054.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___398_6054.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6053  in
                 let s1 =
                   let uu____6059 =
                     let uu____6060 =
                       let uu____6067 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6067)  in
                     FStar_Syntax_Syntax.NT uu____6060  in
                   [uu____6059]  in
                 let uu____6072 = subst_goal bv bv' s1 goal  in
                 (match uu____6072 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6029
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6091 =
      let uu____6094 = cur_goal ()  in
      bind uu____6094
        (fun goal  ->
           let uu____6103 = b  in
           match uu____6103 with
           | (bv,uu____6107) ->
               let uu____6112 =
                 let uu____6121 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6121  in
               (match uu____6112 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6142 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6142 with
                     | (ty,u) ->
                         let uu____6151 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6151
                           (fun uu____6169  ->
                              match uu____6169 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___399_6179 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___399_6179.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___399_6179.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6183 =
                                      let uu____6184 =
                                        let uu____6191 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6191)  in
                                      FStar_Syntax_Syntax.NT uu____6184  in
                                    [uu____6183]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___400_6203 = b1  in
                                         let uu____6204 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___400_6203.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___400_6203.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6204
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6211  ->
                                       let new_goal =
                                         let uu____6213 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6214 =
                                           let uu____6215 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6215
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6213 uu____6214
                                          in
                                       let uu____6216 = add_goals [new_goal]
                                          in
                                       bind uu____6216
                                         (fun uu____6221  ->
                                            let uu____6222 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6222
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6091
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6245 =
        let uu____6248 = cur_goal ()  in
        bind uu____6248
          (fun goal  ->
             let uu____6257 = b  in
             match uu____6257 with
             | (bv,uu____6261) ->
                 let uu____6266 =
                   let uu____6275 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6275  in
                 (match uu____6266 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6299 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6299
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___401_6304 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___401_6304.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___401_6304.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6306 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6306))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6245
  
let (revert : unit -> unit tac) =
  fun uu____6317  ->
    let uu____6320 = cur_goal ()  in
    bind uu____6320
      (fun goal  ->
         let uu____6326 =
           let uu____6333 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6333  in
         match uu____6326 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6349 =
                 let uu____6352 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6352  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6349
                in
             let uu____6367 = new_uvar "revert" env' typ'  in
             bind uu____6367
               (fun uu____6382  ->
                  match uu____6382 with
                  | (r,u_r) ->
                      let uu____6391 =
                        let uu____6394 =
                          let uu____6395 =
                            let uu____6396 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6396.FStar_Syntax_Syntax.pos  in
                          let uu____6399 =
                            let uu____6404 =
                              let uu____6405 =
                                let uu____6414 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6414  in
                              [uu____6405]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6404  in
                          uu____6399 FStar_Pervasives_Native.None uu____6395
                           in
                        set_solution goal uu____6394  in
                      bind uu____6391
                        (fun uu____6435  ->
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
      let uu____6447 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6447
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6462 = cur_goal ()  in
    bind uu____6462
      (fun goal  ->
         mlog
           (fun uu____6470  ->
              let uu____6471 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6472 =
                let uu____6473 =
                  let uu____6474 =
                    let uu____6483 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6483  in
                  FStar_All.pipe_right uu____6474 FStar_List.length  in
                FStar_All.pipe_right uu____6473 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6471 uu____6472)
           (fun uu____6500  ->
              let uu____6501 =
                let uu____6510 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6510  in
              match uu____6501 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6549 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6549
                        then
                          let uu____6552 =
                            let uu____6553 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6553
                             in
                          fail uu____6552
                        else check1 bvs2
                     in
                  let uu____6555 =
                    let uu____6556 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6556  in
                  if uu____6555
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6560 = check1 bvs  in
                     bind uu____6560
                       (fun uu____6566  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6568 =
                            let uu____6575 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6575  in
                          bind uu____6568
                            (fun uu____6584  ->
                               match uu____6584 with
                               | (ut,uvar_ut) ->
                                   let uu____6593 = set_solution goal ut  in
                                   bind uu____6593
                                     (fun uu____6598  ->
                                        let uu____6599 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6599))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6606  ->
    let uu____6609 = cur_goal ()  in
    bind uu____6609
      (fun goal  ->
         let uu____6615 =
           let uu____6622 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6622  in
         match uu____6615 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6630) ->
             let uu____6635 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6635)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6645 = cur_goal ()  in
    bind uu____6645
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6655 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6655  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6658  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6668 = cur_goal ()  in
    bind uu____6668
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6678 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6678  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6681  -> add_goals [g']))
  
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
            let uu____6721 = FStar_Syntax_Subst.compress t  in
            uu____6721.FStar_Syntax_Syntax.n  in
          let uu____6724 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___405_6730 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___405_6730.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___405_6730.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6724
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6746 =
                   let uu____6747 = FStar_Syntax_Subst.compress t1  in
                   uu____6747.FStar_Syntax_Syntax.n  in
                 match uu____6746 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6778 = ff hd1  in
                     bind uu____6778
                       (fun hd2  ->
                          let fa uu____6804 =
                            match uu____6804 with
                            | (a,q) ->
                                let uu____6825 = ff a  in
                                bind uu____6825 (fun a1  -> ret (a1, q))
                             in
                          let uu____6844 = mapM fa args  in
                          bind uu____6844
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6926 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6926 with
                      | (bs1,t') ->
                          let uu____6935 =
                            let uu____6938 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6938 t'  in
                          bind uu____6935
                            (fun t''  ->
                               let uu____6942 =
                                 let uu____6943 =
                                   let uu____6962 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6971 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6962, uu____6971, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6943  in
                               ret uu____6942))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7046 = ff hd1  in
                     bind uu____7046
                       (fun hd2  ->
                          let ffb br =
                            let uu____7061 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7061 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7093 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7093  in
                                let uu____7094 = ff1 e  in
                                bind uu____7094
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7109 = mapM ffb brs  in
                          bind uu____7109
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7153;
                          FStar_Syntax_Syntax.lbtyp = uu____7154;
                          FStar_Syntax_Syntax.lbeff = uu____7155;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7157;
                          FStar_Syntax_Syntax.lbpos = uu____7158;_}::[]),e)
                     ->
                     let lb =
                       let uu____7183 =
                         let uu____7184 = FStar_Syntax_Subst.compress t1  in
                         uu____7184.FStar_Syntax_Syntax.n  in
                       match uu____7183 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7188) -> lb
                       | uu____7201 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7210 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7210
                         (fun def1  ->
                            ret
                              (let uu___402_7216 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___402_7216.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___402_7216.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___402_7216.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___402_7216.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___402_7216.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___402_7216.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7217 = fflb lb  in
                     bind uu____7217
                       (fun lb1  ->
                          let uu____7227 =
                            let uu____7232 =
                              let uu____7233 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7233]  in
                            FStar_Syntax_Subst.open_term uu____7232 e  in
                          match uu____7227 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7263 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7263  in
                              let uu____7264 = ff1 e1  in
                              bind uu____7264
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7305 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7305
                         (fun def  ->
                            ret
                              (let uu___403_7311 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___403_7311.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___403_7311.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___403_7311.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___403_7311.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___403_7311.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___403_7311.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7312 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7312 with
                      | (lbs1,e1) ->
                          let uu____7327 = mapM fflb lbs1  in
                          bind uu____7327
                            (fun lbs2  ->
                               let uu____7339 = ff e1  in
                               bind uu____7339
                                 (fun e2  ->
                                    let uu____7347 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7347 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7415 = ff t2  in
                     bind uu____7415
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7446 = ff t2  in
                     bind uu____7446
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7453 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___404_7460 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___404_7460.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___404_7460.FStar_Syntax_Syntax.vars)
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
            let uu____7497 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___406_7506 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___406_7506.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___406_7506.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___406_7506.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___406_7506.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___406_7506.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___406_7506.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___406_7506.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___406_7506.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___406_7506.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___406_7506.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___406_7506.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___406_7506.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___406_7506.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___406_7506.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___406_7506.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___406_7506.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___406_7506.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___406_7506.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___406_7506.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___406_7506.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___406_7506.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___406_7506.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___406_7506.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___406_7506.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___406_7506.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___406_7506.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___406_7506.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___406_7506.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___406_7506.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___406_7506.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___406_7506.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___406_7506.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___406_7506.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___406_7506.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___406_7506.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___406_7506.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___406_7506.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___406_7506.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___406_7506.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___406_7506.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___406_7506.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7497 with
            | (t1,lcomp,g) ->
                let uu____7512 =
                  (let uu____7515 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7515) ||
                    (let uu____7517 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7517)
                   in
                if uu____7512
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7525 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7525
                       (fun uu____7541  ->
                          match uu____7541 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7554  ->
                                    let uu____7555 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7556 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7555 uu____7556);
                               (let uu____7557 =
                                  let uu____7560 =
                                    let uu____7561 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7561 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7560
                                    opts
                                   in
                                bind uu____7557
                                  (fun uu____7564  ->
                                     let uu____7565 =
                                       bind tau
                                         (fun uu____7571  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7577  ->
                                                 let uu____7578 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7579 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7578 uu____7579);
                                            ret ut1)
                                        in
                                     focus uu____7565))))
                      in
                   let uu____7580 = catch rewrite_eq  in
                   bind uu____7580
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
          let uu____7778 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7778
            (fun t1  ->
               let uu____7786 =
                 f env
                   (let uu___409_7795 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___409_7795.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___409_7795.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7786
                 (fun uu____7811  ->
                    match uu____7811 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7834 =
                               let uu____7835 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7835.FStar_Syntax_Syntax.n  in
                             match uu____7834 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7872 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7872
                                   (fun uu____7897  ->
                                      match uu____7897 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7913 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7913
                                            (fun uu____7940  ->
                                               match uu____7940 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___407_7970 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___407_7970.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___407_7970.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8012 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8012 with
                                  | (bs1,t') ->
                                      let uu____8027 =
                                        let uu____8034 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8034 ctrl1 t'
                                         in
                                      bind uu____8027
                                        (fun uu____8052  ->
                                           match uu____8052 with
                                           | (t'',ctrl2) ->
                                               let uu____8067 =
                                                 let uu____8074 =
                                                   let uu___408_8077 = t4  in
                                                   let uu____8080 =
                                                     let uu____8081 =
                                                       let uu____8100 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8109 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8100,
                                                         uu____8109, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8081
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8080;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___408_8077.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___408_8077.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8074, ctrl2)  in
                                               ret uu____8067))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8162 -> ret (t3, ctrl1))))

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
              let uu____8209 = ctrl_tac_fold f env ctrl t  in
              bind uu____8209
                (fun uu____8233  ->
                   match uu____8233 with
                   | (t1,ctrl1) ->
                       let uu____8248 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8248
                         (fun uu____8275  ->
                            match uu____8275 with
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
              let uu____8359 =
                let uu____8366 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8366
                  (fun uu____8375  ->
                     let uu____8376 = ctrl t1  in
                     bind uu____8376
                       (fun res  ->
                          let uu____8399 = trivial ()  in
                          bind uu____8399 (fun uu____8407  -> ret res)))
                 in
              bind uu____8359
                (fun uu____8423  ->
                   match uu____8423 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8447 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___410_8456 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___410_8456.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___410_8456.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___410_8456.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___410_8456.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___410_8456.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___410_8456.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___410_8456.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___410_8456.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___410_8456.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___410_8456.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___410_8456.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___410_8456.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___410_8456.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___410_8456.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___410_8456.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___410_8456.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___410_8456.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___410_8456.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___410_8456.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___410_8456.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___410_8456.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___410_8456.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___410_8456.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___410_8456.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___410_8456.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___410_8456.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___410_8456.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___410_8456.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___410_8456.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___410_8456.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___410_8456.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___410_8456.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___410_8456.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___410_8456.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___410_8456.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___410_8456.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___410_8456.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___410_8456.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___410_8456.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___410_8456.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___410_8456.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8447 with
                          | (t2,lcomp,g) ->
                              let uu____8466 =
                                (let uu____8469 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8469) ||
                                  (let uu____8471 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8471)
                                 in
                              if uu____8466
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8484 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8484
                                   (fun uu____8504  ->
                                      match uu____8504 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8521  ->
                                                let uu____8522 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8523 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8522 uu____8523);
                                           (let uu____8524 =
                                              let uu____8527 =
                                                let uu____8528 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8528 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8527 opts
                                               in
                                            bind uu____8524
                                              (fun uu____8535  ->
                                                 let uu____8536 =
                                                   bind rewriter
                                                     (fun uu____8550  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8556  ->
                                                             let uu____8557 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8558 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8557
                                                               uu____8558);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8536)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8599 =
        bind get
          (fun ps  ->
             let uu____8609 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8609 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8646  ->
                       let uu____8647 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8647);
                  bind dismiss_all
                    (fun uu____8650  ->
                       let uu____8651 =
                         let uu____8658 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8658
                           keepGoing gt1
                          in
                       bind uu____8651
                         (fun uu____8670  ->
                            match uu____8670 with
                            | (gt',uu____8678) ->
                                (log ps
                                   (fun uu____8682  ->
                                      let uu____8683 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8683);
                                 (let uu____8684 = push_goals gs  in
                                  bind uu____8684
                                    (fun uu____8689  ->
                                       let uu____8690 =
                                         let uu____8693 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8693]  in
                                       add_goals uu____8690)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8599
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8716 =
        bind get
          (fun ps  ->
             let uu____8726 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8726 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8763  ->
                       let uu____8764 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8764);
                  bind dismiss_all
                    (fun uu____8767  ->
                       let uu____8768 =
                         let uu____8771 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8771 gt1
                          in
                       bind uu____8768
                         (fun gt'  ->
                            log ps
                              (fun uu____8779  ->
                                 let uu____8780 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8780);
                            (let uu____8781 = push_goals gs  in
                             bind uu____8781
                               (fun uu____8786  ->
                                  let uu____8787 =
                                    let uu____8790 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8790]  in
                                  add_goals uu____8787))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8716
  
let (trefl : unit -> unit tac) =
  fun uu____8801  ->
    let uu____8804 =
      let uu____8807 = cur_goal ()  in
      bind uu____8807
        (fun g  ->
           let uu____8825 =
             let uu____8830 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8830  in
           match uu____8825 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8838 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8838 with
                | (hd1,args) ->
                    let uu____8877 =
                      let uu____8890 =
                        let uu____8891 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8891.FStar_Syntax_Syntax.n  in
                      (uu____8890, args)  in
                    (match uu____8877 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8905::(l,uu____8907)::(r,uu____8909)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8956 =
                           let uu____8959 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8959 l r  in
                         bind uu____8956
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8966 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8966 l
                                    in
                                 let r1 =
                                   let uu____8968 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8968 r
                                    in
                                 let uu____8969 =
                                   let uu____8972 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8972 l1 r1  in
                                 bind uu____8969
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8978 =
                                           let uu____8979 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8979 l1  in
                                         let uu____8980 =
                                           let uu____8981 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8981 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8978 uu____8980))))
                     | (hd2,uu____8983) ->
                         let uu____9000 =
                           let uu____9001 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9001 t  in
                         fail1 "trefl: not an equality (%s)" uu____9000))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8804
  
let (dup : unit -> unit tac) =
  fun uu____9014  ->
    let uu____9017 = cur_goal ()  in
    bind uu____9017
      (fun g  ->
         let uu____9023 =
           let uu____9030 = FStar_Tactics_Types.goal_env g  in
           let uu____9031 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9030 uu____9031  in
         bind uu____9023
           (fun uu____9040  ->
              match uu____9040 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___411_9050 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___411_9050.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___411_9050.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___411_9050.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9053  ->
                       let uu____9054 =
                         let uu____9057 = FStar_Tactics_Types.goal_env g  in
                         let uu____9058 =
                           let uu____9059 =
                             let uu____9060 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9061 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9060
                               uu____9061
                              in
                           let uu____9062 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9063 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9059 uu____9062 u
                             uu____9063
                            in
                         add_irrelevant_goal "dup equation" uu____9057
                           uu____9058 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9054
                         (fun uu____9066  ->
                            let uu____9067 = add_goals [g']  in
                            bind uu____9067 (fun uu____9071  -> ret ())))))
  
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
              let uu____9194 = f x y  in
              if uu____9194 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9214 -> (acc, l11, l21)  in
        let uu____9229 = aux [] l1 l2  in
        match uu____9229 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9334 = get_phi g1  in
      match uu____9334 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9340 = get_phi g2  in
          (match uu____9340 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9352 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9352 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9383 =
                        FStar_TypeChecker_Env.binders_of_bindings r1  in
                      close_forall_no_univs1 uu____9383 phi1  in
                    let t2 =
                      let uu____9393 =
                        FStar_TypeChecker_Env.binders_of_bindings r2  in
                      close_forall_no_univs1 uu____9393 phi2  in
                    let uu____9402 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9402
                      (fun uu____9407  ->
                         let uu____9408 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9408
                           (fun uu____9415  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___412_9420 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9421 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___412_9420.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___412_9420.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___412_9420.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___412_9420.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9421;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___412_9420.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___412_9420.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___412_9420.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___412_9420.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___412_9420.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___412_9420.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___412_9420.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___412_9420.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___412_9420.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___412_9420.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___412_9420.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___412_9420.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___412_9420.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___412_9420.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___412_9420.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___412_9420.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___412_9420.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___412_9420.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___412_9420.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___412_9420.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___412_9420.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___412_9420.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___412_9420.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___412_9420.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___412_9420.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___412_9420.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___412_9420.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___412_9420.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___412_9420.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___412_9420.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___412_9420.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___412_9420.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___412_9420.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___412_9420.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.dep_graph =
                                    (uu___412_9420.FStar_TypeChecker_Env.dep_graph);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___412_9420.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9424 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9424
                                (fun goal  ->
                                   mlog
                                     (fun uu____9433  ->
                                        let uu____9434 =
                                          goal_to_string_verbose g1  in
                                        let uu____9435 =
                                          goal_to_string_verbose g2  in
                                        let uu____9436 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9434 uu____9435 uu____9436)
                                     (fun uu____9438  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9445  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9461 =
               set
                 (let uu___413_9466 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___413_9466.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___413_9466.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___413_9466.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___413_9466.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___413_9466.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___413_9466.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___413_9466.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___413_9466.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___413_9466.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___413_9466.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___413_9466.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___413_9466.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9461
               (fun uu____9469  ->
                  let uu____9470 = join_goals g1 g2  in
                  bind uu____9470 (fun g12  -> add_goals [g12]))
         | uu____9475 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9495 =
      let uu____9502 = cur_goal ()  in
      bind uu____9502
        (fun g  ->
           let uu____9512 =
             let uu____9521 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9521 t  in
           bind uu____9512
             (fun uu____9549  ->
                match uu____9549 with
                | (t1,typ,guard) ->
                    let uu____9565 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9565 with
                     | (hd1,args) ->
                         let uu____9614 =
                           let uu____9629 =
                             let uu____9630 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9630.FStar_Syntax_Syntax.n  in
                           (uu____9629, args)  in
                         (match uu____9614 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9651)::(q,uu____9653)::[]) when
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
                                let uu____9707 =
                                  let uu____9708 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9708
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9707
                                 in
                              let g2 =
                                let uu____9710 =
                                  let uu____9711 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9711
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9710
                                 in
                              bind __dismiss
                                (fun uu____9718  ->
                                   let uu____9719 = add_goals [g1; g2]  in
                                   bind uu____9719
                                     (fun uu____9728  ->
                                        let uu____9729 =
                                          let uu____9734 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9735 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9734, uu____9735)  in
                                        ret uu____9729))
                          | uu____9740 ->
                              let uu____9755 =
                                let uu____9756 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9756 typ  in
                              fail1 "Not a disjunction: %s" uu____9755))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9495
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9786 =
      let uu____9789 = cur_goal ()  in
      bind uu____9789
        (fun g  ->
           FStar_Options.push ();
           (let uu____9802 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9802);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___414_9809 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___414_9809.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___414_9809.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___414_9809.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9786
  
let (top_env : unit -> env tac) =
  fun uu____9821  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9834  ->
    let uu____9837 = cur_goal ()  in
    bind uu____9837
      (fun g  ->
         let uu____9843 =
           (FStar_Options.lax ()) ||
             (let uu____9845 = FStar_Tactics_Types.goal_env g  in
              uu____9845.FStar_TypeChecker_Env.lax)
            in
         ret uu____9843)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9860 =
        mlog
          (fun uu____9865  ->
             let uu____9866 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9866)
          (fun uu____9869  ->
             let uu____9870 = cur_goal ()  in
             bind uu____9870
               (fun goal  ->
                  let env =
                    let uu____9878 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9878 ty  in
                  let uu____9879 = __tc env tm  in
                  bind uu____9879
                    (fun uu____9898  ->
                       match uu____9898 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9912  ->
                                let uu____9913 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9913)
                             (fun uu____9915  ->
                                mlog
                                  (fun uu____9918  ->
                                     let uu____9919 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9919)
                                  (fun uu____9922  ->
                                     let uu____9923 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9923
                                       (fun uu____9927  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9860
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9950 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9956 =
              let uu____9963 =
                let uu____9964 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9964
                 in
              new_uvar "uvar_env.2" env uu____9963  in
            bind uu____9956
              (fun uu____9980  ->
                 match uu____9980 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9950
        (fun typ  ->
           let uu____9992 = new_uvar "uvar_env" env typ  in
           bind uu____9992
             (fun uu____10006  ->
                match uu____10006 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10024 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10043 -> g.FStar_Tactics_Types.opts
             | uu____10046 -> FStar_Options.peek ()  in
           let uu____10049 = FStar_Syntax_Util.head_and_args t  in
           match uu____10049 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10069);
                FStar_Syntax_Syntax.pos = uu____10070;
                FStar_Syntax_Syntax.vars = uu____10071;_},uu____10072)
               ->
               let env1 =
                 let uu___415_10114 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___415_10114.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___415_10114.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___415_10114.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___415_10114.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___415_10114.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___415_10114.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___415_10114.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___415_10114.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___415_10114.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___415_10114.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___415_10114.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___415_10114.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___415_10114.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___415_10114.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___415_10114.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___415_10114.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___415_10114.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___415_10114.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___415_10114.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___415_10114.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___415_10114.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___415_10114.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___415_10114.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___415_10114.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___415_10114.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___415_10114.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___415_10114.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___415_10114.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___415_10114.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___415_10114.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___415_10114.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___415_10114.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___415_10114.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___415_10114.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___415_10114.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___415_10114.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___415_10114.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___415_10114.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___415_10114.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___415_10114.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___415_10114.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10116 =
                 let uu____10119 = bnorm_goal g  in [uu____10119]  in
               add_goals uu____10116
           | uu____10120 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10024
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10169 = if b then t2 else ret false  in
             bind uu____10169 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10180 = trytac comp  in
      bind uu____10180
        (fun uu___351_10188  ->
           match uu___351_10188 with
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
        let uu____10214 =
          bind get
            (fun ps  ->
               let uu____10220 = __tc e t1  in
               bind uu____10220
                 (fun uu____10240  ->
                    match uu____10240 with
                    | (t11,ty1,g1) ->
                        let uu____10252 = __tc e t2  in
                        bind uu____10252
                          (fun uu____10272  ->
                             match uu____10272 with
                             | (t21,ty2,g2) ->
                                 let uu____10284 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10284
                                   (fun uu____10289  ->
                                      let uu____10290 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10290
                                        (fun uu____10296  ->
                                           let uu____10297 =
                                             do_unify e ty1 ty2  in
                                           let uu____10300 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10297 uu____10300)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10214
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10333  ->
             let uu____10334 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10334
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
        (fun uu____10355  ->
           let uu____10356 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10356)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10366 =
      mlog
        (fun uu____10371  ->
           let uu____10372 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10372)
        (fun uu____10375  ->
           let uu____10376 = cur_goal ()  in
           bind uu____10376
             (fun g  ->
                let uu____10382 =
                  let uu____10391 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10391 ty  in
                bind uu____10382
                  (fun uu____10403  ->
                     match uu____10403 with
                     | (ty1,uu____10413,guard) ->
                         let uu____10415 =
                           let uu____10418 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10418 guard  in
                         bind uu____10415
                           (fun uu____10421  ->
                              let uu____10422 =
                                let uu____10425 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10426 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10425 uu____10426 ty1  in
                              bind uu____10422
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10432 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10432
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10438 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10439 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10438
                                          uu____10439
                                         in
                                      let nty =
                                        let uu____10441 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10441 ty1  in
                                      let uu____10442 =
                                        let uu____10445 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10445 ng nty  in
                                      bind uu____10442
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10451 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10451
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10366
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10514 =
      let uu____10523 = cur_goal ()  in
      bind uu____10523
        (fun g  ->
           let uu____10535 =
             let uu____10544 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10544 s_tm  in
           bind uu____10535
             (fun uu____10562  ->
                match uu____10562 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10580 =
                      let uu____10583 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10583 guard  in
                    bind uu____10580
                      (fun uu____10595  ->
                         let uu____10596 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10596 with
                         | (h,args) ->
                             let uu____10641 =
                               let uu____10648 =
                                 let uu____10649 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10649.FStar_Syntax_Syntax.n  in
                               match uu____10648 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10664;
                                      FStar_Syntax_Syntax.vars = uu____10665;_},us)
                                   -> ret (fv, us)
                               | uu____10675 -> fail "type is not an fv"  in
                             bind uu____10641
                               (fun uu____10695  ->
                                  match uu____10695 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10711 =
                                        let uu____10714 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10714 t_lid
                                         in
                                      (match uu____10711 with
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
                                                  (fun uu____10763  ->
                                                     let uu____10764 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10764 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10779 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10807
                                                                  =
                                                                  let uu____10810
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10810
                                                                    c_lid
                                                                   in
                                                                match uu____10807
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
                                                                    uu____10880
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
                                                                    let uu____10885
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10885
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10908
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10908
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10951
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10951
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11024
                                                                    =
                                                                    let uu____11025
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11025
                                                                     in
                                                                    failwhen
                                                                    uu____11024
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11042
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
                                                                    uu___352_11058
                                                                    =
                                                                    match uu___352_11058
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11061)
                                                                    -> true
                                                                    | 
                                                                    uu____11062
                                                                    -> false
                                                                     in
                                                                    let uu____11065
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11065
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
                                                                    uu____11198
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
                                                                    uu____11260
                                                                     ->
                                                                    match uu____11260
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11280),
                                                                    (t,uu____11282))
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
                                                                    uu____11350
                                                                     ->
                                                                    match uu____11350
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11376),
                                                                    (t,uu____11378))
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
                                                                    uu____11433
                                                                     ->
                                                                    match uu____11433
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
                                                                    let uu____11483
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___416_11500
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___416_11500.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11483
                                                                    with
                                                                    | 
                                                                    (uu____11513,uu____11514,uu____11515,pat_t,uu____11517,uu____11518)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11524
                                                                    =
                                                                    let uu____11525
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11525
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11524
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11529
                                                                    =
                                                                    let uu____11538
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11538]
                                                                     in
                                                                    let uu____11557
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11529
                                                                    uu____11557
                                                                     in
                                                                    let nty =
                                                                    let uu____11563
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11563
                                                                     in
                                                                    let uu____11566
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11566
                                                                    (fun
                                                                    uu____11595
                                                                     ->
                                                                    match uu____11595
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
                                                                    let uu____11621
                                                                    =
                                                                    let uu____11632
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11632]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11621
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11668
                                                                    =
                                                                    let uu____11679
                                                                    =
                                                                    let uu____11684
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11684)
                                                                     in
                                                                    (g', br,
                                                                    uu____11679)
                                                                     in
                                                                    ret
                                                                    uu____11668))))))
                                                                    | 
                                                                    uu____11705
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10779
                                                           (fun goal_brs  ->
                                                              let uu____11754
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11754
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
                                                                  let uu____11827
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11827
                                                                    (
                                                                    fun
                                                                    uu____11838
                                                                     ->
                                                                    let uu____11839
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11839
                                                                    (fun
                                                                    uu____11849
                                                                     ->
                                                                    ret infos))))
                                            | uu____11856 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10514
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11901::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11929 = init xs  in x :: uu____11929
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11941 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____11950) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12015 = last args  in
          (match uu____12015 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12045 =
                 let uu____12046 =
                   let uu____12051 =
                     let uu____12052 =
                       let uu____12057 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12057  in
                     uu____12052 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12051, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12046  in
               FStar_All.pipe_left ret uu____12045)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12070,uu____12071) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12123 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12123 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12164 =
                      let uu____12165 =
                        let uu____12170 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12170)  in
                      FStar_Reflection_Data.Tv_Abs uu____12165  in
                    FStar_All.pipe_left ret uu____12164))
      | FStar_Syntax_Syntax.Tm_type uu____12173 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12197 ->
          let uu____12212 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12212 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12242 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12242 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12295 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12307 =
            let uu____12308 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12308  in
          FStar_All.pipe_left ret uu____12307
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12329 =
            let uu____12330 =
              let uu____12335 =
                let uu____12336 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12336  in
              (uu____12335, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12330  in
          FStar_All.pipe_left ret uu____12329
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12370 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12375 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12375 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12428 ->
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
             | FStar_Util.Inr uu____12462 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12466 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12466 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12486 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12490 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12544 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12544
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12563 =
                  let uu____12570 =
                    FStar_List.map
                      (fun uu____12582  ->
                         match uu____12582 with
                         | (p1,uu____12590) -> inspect_pat p1) ps
                     in
                  (fv, uu____12570)  in
                FStar_Reflection_Data.Pat_Cons uu____12563
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
              (fun uu___353_12684  ->
                 match uu___353_12684 with
                 | (pat,uu____12706,t5) ->
                     let uu____12724 = inspect_pat pat  in (uu____12724, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12733 ->
          ((let uu____12735 =
              let uu____12740 =
                let uu____12741 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12742 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12741 uu____12742
                 in
              (FStar_Errors.Warning_CantInspect, uu____12740)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12735);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11941
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12755 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12755
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12759 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12759
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12763 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12763
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12770 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12770
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12795 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12795
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12812 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12812
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12831 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12831
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12835 =
          let uu____12836 =
            let uu____12843 =
              let uu____12844 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12844  in
            FStar_Syntax_Syntax.mk uu____12843  in
          uu____12836 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12835
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12852 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12852
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12861 =
          let uu____12862 =
            let uu____12869 =
              let uu____12870 =
                let uu____12883 =
                  let uu____12886 =
                    let uu____12887 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12887]  in
                  FStar_Syntax_Subst.close uu____12886 t2  in
                ((false, [lb]), uu____12883)  in
              FStar_Syntax_Syntax.Tm_let uu____12870  in
            FStar_Syntax_Syntax.mk uu____12869  in
          uu____12862 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12861
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12927 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12927 with
         | (lbs,body) ->
             let uu____12942 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12942)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12976 =
                let uu____12977 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12977  in
              FStar_All.pipe_left wrap uu____12976
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12984 =
                let uu____12985 =
                  let uu____12998 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13014 = pack_pat p1  in
                         (uu____13014, false)) ps
                     in
                  (fv, uu____12998)  in
                FStar_Syntax_Syntax.Pat_cons uu____12985  in
              FStar_All.pipe_left wrap uu____12984
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
            (fun uu___354_13060  ->
               match uu___354_13060 with
               | (pat,t1) ->
                   let uu____13077 = pack_pat pat  in
                   (uu____13077, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13125 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13125
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13153 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13153
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13199 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13199
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13238 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13238
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13255 =
        bind get
          (fun ps  ->
             let uu____13261 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13261 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13255
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13290 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___417_13297 = ps  in
                 let uu____13298 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___417_13297.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___417_13297.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___417_13297.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___417_13297.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___417_13297.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___417_13297.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___417_13297.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___417_13297.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___417_13297.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___417_13297.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___417_13297.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___417_13297.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13298
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13290
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13323 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13323 with
      | (u,ctx_uvars,g_u) ->
          let uu____13355 = FStar_List.hd ctx_uvars  in
          (match uu____13355 with
           | (ctx_uvar,uu____13369) ->
               let g =
                 let uu____13371 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13371 false
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
        let uu____13391 = goal_of_goal_ty env typ  in
        match uu____13391 with
        | (g,g_u) ->
            let ps =
              let uu____13403 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13404 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13403;
                FStar_Tactics_Types.local_state = uu____13404
              }  in
            let uu____13411 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13411)
  