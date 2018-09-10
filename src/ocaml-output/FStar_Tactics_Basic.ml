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
        (try (fun uu___360_158  -> match () with | () -> run t p) ()
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
  Prims.string ->
    (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option ->
      FStar_Tactics_Types.proofstate ->
        FStar_Tactics_Types.goal -> Prims.string)
  =
  fun kind  ->
    fun maybe_num  ->
      fun ps  ->
        fun g  ->
          let uu____334 =
            (FStar_Options.print_implicits ()) ||
              ps.FStar_Tactics_Types.tac_verb_dbg
             in
          if uu____334
          then goal_to_string_verbose g
          else
            (let w =
               let uu____337 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____337 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____341 = FStar_Tactics_Types.goal_env g  in
                   tts uu____341 t
                in
             let num =
               match maybe_num with
               | FStar_Pervasives_Native.None  -> ""
               | FStar_Pervasives_Native.Some (i,n1) ->
                   let uu____353 = FStar_Util.string_of_int i  in
                   let uu____354 = FStar_Util.string_of_int n1  in
                   FStar_Util.format2 " %s/%s" uu____353 uu____354
                in
             let maybe_label =
               match g.FStar_Tactics_Types.label with
               | "" -> ""
               | l -> Prims.strcat " (" (Prims.strcat l ")")  in
             let uu____357 =
               FStar_Syntax_Print.binders_to_string ", "
                 (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                in
             let uu____358 =
               let uu____359 = FStar_Tactics_Types.goal_env g  in
               tts uu____359
                 (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                in
             FStar_Util.format6 "%s%s%s:\n%s |- %s : %s\n\n" kind num
               maybe_label uu____357 w uu____358)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____375 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____375
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____391 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____391
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____412 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____412
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____419) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____429) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____448 =
      let uu____449 = FStar_Tactics_Types.goal_env g  in
      let uu____450 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____449 uu____450  in
    FStar_Syntax_Util.un_squash uu____448
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____456 = get_phi g  in FStar_Option.isSome uu____456 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____475  ->
    bind get
      (fun ps  ->
         let uu____481 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____481)
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____490  ->
    match uu____490 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____516 =
          let uu____519 =
            let uu____522 =
              let uu____523 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____523
                msg
               in
            let uu____524 =
              let uu____527 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____528 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____528
                else ""  in
              let uu____530 =
                let uu____533 =
                  let uu____534 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____534
                  then
                    let uu____535 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____535
                  else ""  in
                [uu____533]  in
              uu____527 :: uu____530  in
            uu____522 :: uu____524  in
          let uu____537 =
            let uu____540 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____551 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____540 uu____551  in
          FStar_List.append uu____519 uu____537  in
        FStar_String.concat "" uu____516
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____572 =
        let uu____573 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____573  in
      let uu____574 =
        let uu____579 =
          let uu____580 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____580  in
        FStar_Syntax_Print.binders_to_json uu____579  in
      FStar_All.pipe_right uu____572 uu____574  in
    let uu____581 =
      let uu____588 =
        let uu____595 =
          let uu____600 =
            let uu____601 =
              let uu____608 =
                let uu____613 =
                  let uu____614 =
                    let uu____615 = FStar_Tactics_Types.goal_env g  in
                    let uu____616 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____615 uu____616  in
                  FStar_Util.JsonStr uu____614  in
                ("witness", uu____613)  in
              let uu____617 =
                let uu____624 =
                  let uu____629 =
                    let uu____630 =
                      let uu____631 = FStar_Tactics_Types.goal_env g  in
                      let uu____632 = FStar_Tactics_Types.goal_type g  in
                      tts uu____631 uu____632  in
                    FStar_Util.JsonStr uu____630  in
                  ("type", uu____629)  in
                [uu____624;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____608 :: uu____617  in
            FStar_Util.JsonAssoc uu____601  in
          ("goal", uu____600)  in
        [uu____595]  in
      ("hyps", g_binders) :: uu____588  in
    FStar_Util.JsonAssoc uu____581
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____669  ->
    match uu____669 with
    | (msg,ps) ->
        let uu____676 =
          let uu____683 =
            let uu____690 =
              let uu____697 =
                let uu____704 =
                  let uu____709 =
                    let uu____710 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____710  in
                  ("goals", uu____709)  in
                let uu____713 =
                  let uu____720 =
                    let uu____725 =
                      let uu____726 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____726  in
                    ("smt-goals", uu____725)  in
                  [uu____720]  in
                uu____704 :: uu____713  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____697
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____690  in
          let uu____749 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____762 =
                let uu____767 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____767)  in
              [uu____762]
            else []  in
          FStar_List.append uu____683 uu____749  in
        FStar_Util.JsonAssoc uu____676
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____797  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____820 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____820 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____874 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____874
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____882 . Prims.string -> Prims.string -> 'Auu____882 tac =
  fun msg  ->
    fun x  -> let uu____895 = FStar_Util.format1 msg x  in fail uu____895
  
let fail2 :
  'Auu____904 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____904 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____922 = FStar_Util.format2 msg x y  in fail uu____922
  
let fail3 :
  'Auu____933 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____933 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____956 = FStar_Util.format3 msg x y z  in fail uu____956
  
let fail4 :
  'Auu____969 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____969 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____997 = FStar_Util.format4 msg x y z w  in fail uu____997
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1030 = run t ps  in
         match uu____1030 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___361_1054 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___361_1054.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___361_1054.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___361_1054.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___361_1054.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___361_1054.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___361_1054.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___361_1054.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___361_1054.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___361_1054.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___361_1054.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___361_1054.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___361_1054.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1081 = catch t  in
    bind uu____1081
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1108 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___363_1139  ->
              match () with
              | () -> let uu____1144 = trytac t  in run uu____1144 ps) ()
         with
         | FStar_Errors.Err (uu____1160,msg) ->
             (log ps
                (fun uu____1164  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1169,msg,uu____1171) ->
             (log ps
                (fun uu____1174  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1207 = run t ps  in
           match uu____1207 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1226  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___364_1240 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___364_1240.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___364_1240.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___364_1240.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___364_1240.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___364_1240.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___364_1240.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___364_1240.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___364_1240.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___364_1240.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___364_1240.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___364_1240.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___364_1240.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1261 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1261
         then
           let uu____1262 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1263 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1262
             uu____1263
         else ());
        (try
           (fun uu___366_1270  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1277 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1277
                    then
                      let uu____1278 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1279 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1280 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1278
                        uu____1279 uu____1280
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1285 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1285 (fun uu____1289  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1296,msg) ->
             mlog
               (fun uu____1299  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1301  -> ret false)
         | FStar_Errors.Error (uu____1302,msg,r) ->
             mlog
               (fun uu____1307  ->
                  let uu____1308 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1308) (fun uu____1310  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___367_1321 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___367_1321.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___367_1321.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___367_1321.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___368_1324 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___368_1324.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___368_1324.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___368_1324.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___368_1324.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___368_1324.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___368_1324.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___368_1324.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___368_1324.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___368_1324.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___368_1324.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___368_1324.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___368_1324.FStar_Tactics_Types.local_state)
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
          (fun uu____1347  ->
             (let uu____1349 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1349
              then
                (FStar_Options.push ();
                 (let uu____1351 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1353 = __do_unify env t1 t2  in
              bind uu____1353
                (fun r  ->
                   (let uu____1360 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1360 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1363  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___369_1370 = ps  in
         let uu____1371 =
           FStar_List.filter
             (fun g  ->
                let uu____1377 = check_goal_solved g  in
                FStar_Option.isNone uu____1377) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___369_1370.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___369_1370.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___369_1370.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1371;
           FStar_Tactics_Types.smt_goals =
             (uu___369_1370.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___369_1370.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___369_1370.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___369_1370.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___369_1370.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___369_1370.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___369_1370.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___369_1370.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___369_1370.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1394 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1394 with
      | FStar_Pervasives_Native.Some uu____1399 ->
          let uu____1400 =
            let uu____1401 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1401  in
          fail uu____1400
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1417 = FStar_Tactics_Types.goal_env goal  in
      let uu____1418 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1417 solution uu____1418
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1424 =
         let uu___370_1425 = p  in
         let uu____1426 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___370_1425.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___370_1425.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___370_1425.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1426;
           FStar_Tactics_Types.smt_goals =
             (uu___370_1425.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___370_1425.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___370_1425.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___370_1425.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___370_1425.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___370_1425.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___370_1425.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___370_1425.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___370_1425.FStar_Tactics_Types.local_state)
         }  in
       set uu____1424)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1447  ->
           let uu____1448 =
             let uu____1449 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1449  in
           let uu____1450 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1448 uu____1450)
        (fun uu____1453  ->
           let uu____1454 = trysolve goal solution  in
           bind uu____1454
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1462  -> remove_solved_goals)
                else
                  (let uu____1464 =
                     let uu____1465 =
                       let uu____1466 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1466 solution  in
                     let uu____1467 =
                       let uu____1468 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1469 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1468 uu____1469  in
                     let uu____1470 =
                       let uu____1471 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1472 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1471 uu____1472  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1465 uu____1467 uu____1470
                      in
                   fail uu____1464)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1487 = set_solution goal solution  in
      bind uu____1487
        (fun uu____1491  ->
           bind __dismiss (fun uu____1493  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___371_1511 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1511.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1511.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1511.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___371_1511.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___371_1511.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1511.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1511.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1511.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1511.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1511.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1511.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1511.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___372_1529 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1529.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1529.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_1529.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___372_1529.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___372_1529.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1529.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1529.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1529.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_1529.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_1529.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_1529.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_1529.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1550 = FStar_Options.defensive ()  in
    if uu____1550
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1555 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1555)
         in
      let b2 =
        b1 &&
          (let uu____1558 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1558)
         in
      let rec aux b3 e =
        let uu____1570 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1570 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1588 =
        (let uu____1591 = aux b2 env  in Prims.op_Negation uu____1591) &&
          (let uu____1593 = FStar_ST.op_Bang nwarn  in
           uu____1593 < (Prims.parse_int "5"))
         in
      (if uu____1588
       then
         ((let uu____1614 =
             let uu____1615 = FStar_Tactics_Types.goal_type g  in
             uu____1615.FStar_Syntax_Syntax.pos  in
           let uu____1618 =
             let uu____1623 =
               let uu____1624 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1624
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1623)  in
           FStar_Errors.log_issue uu____1614 uu____1618);
          (let uu____1625 =
             let uu____1626 = FStar_ST.op_Bang nwarn  in
             uu____1626 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1625))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___373_1686 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___373_1686.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___373_1686.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___373_1686.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___373_1686.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___373_1686.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___373_1686.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___373_1686.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___373_1686.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___373_1686.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___373_1686.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___373_1686.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___373_1686.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___374_1706 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_1706.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_1706.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___374_1706.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___374_1706.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___374_1706.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_1706.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_1706.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_1706.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___374_1706.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___374_1706.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_1706.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_1706.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___375_1726 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___375_1726.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___375_1726.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___375_1726.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___375_1726.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___375_1726.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___375_1726.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___375_1726.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___375_1726.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___375_1726.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___375_1726.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___375_1726.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___375_1726.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___376_1746 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___376_1746.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___376_1746.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___376_1746.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___376_1746.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___376_1746.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___376_1746.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___376_1746.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___376_1746.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___376_1746.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___376_1746.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___376_1746.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___376_1746.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1757  -> add_goals [g]) 
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
        let uu____1785 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1785 with
        | (u,ctx_uvar,g_u) ->
            let uu____1819 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1819
              (fun uu____1828  ->
                 let uu____1829 =
                   let uu____1834 =
                     let uu____1835 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1835  in
                   (u, uu____1834)  in
                 ret uu____1829)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1853 = FStar_Syntax_Util.un_squash t  in
    match uu____1853 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1863 =
          let uu____1864 = FStar_Syntax_Subst.compress t'  in
          uu____1864.FStar_Syntax_Syntax.n  in
        (match uu____1863 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1868 -> false)
    | uu____1869 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1879 = FStar_Syntax_Util.un_squash t  in
    match uu____1879 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1889 =
          let uu____1890 = FStar_Syntax_Subst.compress t'  in
          uu____1890.FStar_Syntax_Syntax.n  in
        (match uu____1889 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1894 -> false)
    | uu____1895 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1906  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1917 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1917 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1924 = goal_to_string_verbose hd1  in
                    let uu____1925 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1924 uu____1925);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____1935 =
      bind get
        (fun ps  ->
           let uu____1941 = cur_goal ()  in
           bind uu____1941
             (fun g  ->
                (let uu____1948 =
                   let uu____1949 = FStar_Tactics_Types.goal_type g  in
                   uu____1949.FStar_Syntax_Syntax.pos  in
                 let uu____1952 =
                   let uu____1957 =
                     let uu____1958 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1958
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1957)  in
                 FStar_Errors.log_issue uu____1948 uu____1952);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____1935
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1973  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___377_1983 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___377_1983.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___377_1983.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___377_1983.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___377_1983.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___377_1983.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___377_1983.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___377_1983.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___377_1983.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___377_1983.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___377_1983.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___377_1983.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___377_1983.FStar_Tactics_Types.local_state)
           }  in
         let uu____1984 = set ps1  in
         bind uu____1984
           (fun uu____1989  ->
              let uu____1990 = FStar_BigInt.of_int_fs n1  in ret uu____1990))
  
let (mk_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate ->
          Prims.string -> FStar_Tactics_Types.goal tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let typ =
              let uu____2023 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2023 phi  in
            let uu____2024 = new_uvar reason env typ  in
            bind uu____2024
              (fun uu____2039  ->
                 match uu____2039 with
                 | (uu____2046,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1
                        in
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
             (fun uu____2091  ->
                let uu____2092 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2092)
             (fun uu____2095  ->
                let e1 =
                  let uu___378_2097 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___378_2097.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___378_2097.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___378_2097.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___378_2097.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___378_2097.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___378_2097.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___378_2097.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___378_2097.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___378_2097.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___378_2097.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___378_2097.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___378_2097.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___378_2097.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___378_2097.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___378_2097.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___378_2097.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___378_2097.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___378_2097.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___378_2097.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___378_2097.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___378_2097.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___378_2097.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___378_2097.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___378_2097.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___378_2097.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___378_2097.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___378_2097.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___378_2097.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___378_2097.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___378_2097.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___378_2097.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___378_2097.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___378_2097.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___378_2097.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___378_2097.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___378_2097.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___378_2097.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___378_2097.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___378_2097.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___378_2097.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___378_2097.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___378_2097.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___380_2108  ->
                     match () with
                     | () ->
                         let uu____2117 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2117) ()
                with
                | FStar_Errors.Err (uu____2144,msg) ->
                    let uu____2146 = tts e1 t  in
                    let uu____2147 =
                      let uu____2148 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2148
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2146 uu____2147 msg
                | FStar_Errors.Error (uu____2155,msg,uu____2157) ->
                    let uu____2158 = tts e1 t  in
                    let uu____2159 =
                      let uu____2160 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2160
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2158 uu____2159 msg))
  
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
             (fun uu____2209  ->
                let uu____2210 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2210)
             (fun uu____2213  ->
                let e1 =
                  let uu___381_2215 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___381_2215.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___381_2215.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___381_2215.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___381_2215.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___381_2215.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___381_2215.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___381_2215.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___381_2215.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___381_2215.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___381_2215.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___381_2215.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___381_2215.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___381_2215.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___381_2215.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___381_2215.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___381_2215.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___381_2215.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___381_2215.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___381_2215.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___381_2215.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___381_2215.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___381_2215.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___381_2215.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___381_2215.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___381_2215.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___381_2215.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___381_2215.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___381_2215.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___381_2215.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___381_2215.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___381_2215.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___381_2215.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___381_2215.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___381_2215.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___381_2215.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___381_2215.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___381_2215.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___381_2215.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___381_2215.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___381_2215.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___381_2215.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___381_2215.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___383_2229  ->
                     match () with
                     | () ->
                         let uu____2238 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2238 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2276,msg) ->
                    let uu____2278 = tts e1 t  in
                    let uu____2279 =
                      let uu____2280 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2280
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2278 uu____2279 msg
                | FStar_Errors.Error (uu____2287,msg,uu____2289) ->
                    let uu____2290 = tts e1 t  in
                    let uu____2291 =
                      let uu____2292 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2292
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2290 uu____2291 msg))
  
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
             (fun uu____2341  ->
                let uu____2342 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2342)
             (fun uu____2346  ->
                let e1 =
                  let uu___384_2348 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___384_2348.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___384_2348.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___384_2348.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___384_2348.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___384_2348.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___384_2348.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___384_2348.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___384_2348.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___384_2348.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___384_2348.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___384_2348.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___384_2348.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___384_2348.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___384_2348.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___384_2348.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___384_2348.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___384_2348.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___384_2348.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___384_2348.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___384_2348.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___384_2348.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___384_2348.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___384_2348.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___384_2348.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___384_2348.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___384_2348.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___384_2348.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___384_2348.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___384_2348.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___384_2348.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___384_2348.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___384_2348.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___384_2348.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___384_2348.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___384_2348.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___384_2348.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___384_2348.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___384_2348.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___384_2348.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___384_2348.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___384_2348.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___384_2348.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___385_2350 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___385_2350.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___385_2350.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___385_2350.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___385_2350.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___385_2350.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___385_2350.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___385_2350.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___385_2350.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___385_2350.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___385_2350.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___385_2350.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___385_2350.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___385_2350.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___385_2350.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___385_2350.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___385_2350.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___385_2350.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___385_2350.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___385_2350.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___385_2350.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___385_2350.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___385_2350.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___385_2350.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___385_2350.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___385_2350.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___385_2350.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___385_2350.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___385_2350.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___385_2350.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___385_2350.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___385_2350.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___385_2350.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___385_2350.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___385_2350.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___385_2350.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___385_2350.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___385_2350.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___385_2350.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___385_2350.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___385_2350.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___385_2350.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___385_2350.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___387_2364  ->
                     match () with
                     | () ->
                         let uu____2373 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2373 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2411,msg) ->
                    let uu____2413 = tts e2 t  in
                    let uu____2414 =
                      let uu____2415 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2415
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2413 uu____2414 msg
                | FStar_Errors.Error (uu____2422,msg,uu____2424) ->
                    let uu____2425 = tts e2 t  in
                    let uu____2426 =
                      let uu____2427 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2427
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2425 uu____2426 msg))
  
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
  fun uu____2454  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___388_2472 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___388_2472.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___388_2472.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___388_2472.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___388_2472.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___388_2472.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___388_2472.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___388_2472.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___388_2472.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___388_2472.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___388_2472.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___388_2472.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___388_2472.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2496 = get_guard_policy ()  in
      bind uu____2496
        (fun old_pol  ->
           let uu____2502 = set_guard_policy pol  in
           bind uu____2502
             (fun uu____2506  ->
                bind t
                  (fun r  ->
                     let uu____2510 = set_guard_policy old_pol  in
                     bind uu____2510 (fun uu____2514  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2517 = let uu____2522 = cur_goal ()  in trytac uu____2522  in
  bind uu____2517
    (fun uu___351_2529  ->
       match uu___351_2529 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2535 = FStar_Options.peek ()  in ret uu____2535)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2557  ->
             let uu____2558 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2558)
          (fun uu____2561  ->
             let uu____2562 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2562
               (fun uu____2566  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2570 =
                         let uu____2571 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2571.FStar_TypeChecker_Env.guard_f  in
                       match uu____2570 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2575 = istrivial e f  in
                           if uu____2575
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2585 =
                                          let uu____2590 =
                                            let uu____2591 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2591
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2590)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2585);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2594  ->
                                           let uu____2595 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2595)
                                        (fun uu____2598  ->
                                           let uu____2599 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2599
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___389_2606 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___389_2606.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___389_2606.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___389_2606.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___389_2606.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2609  ->
                                           let uu____2610 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2610)
                                        (fun uu____2613  ->
                                           let uu____2614 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2614
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___390_2621 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___390_2621.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___390_2621.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___390_2621.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___390_2621.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2624  ->
                                           let uu____2625 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2625)
                                        (fun uu____2627  ->
                                           try
                                             (fun uu___392_2632  ->
                                                match () with
                                                | () ->
                                                    let uu____2635 =
                                                      let uu____2636 =
                                                        let uu____2637 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2637
                                                         in
                                                      Prims.op_Negation
                                                        uu____2636
                                                       in
                                                    if uu____2635
                                                    then
                                                      mlog
                                                        (fun uu____2642  ->
                                                           let uu____2643 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2643)
                                                        (fun uu____2645  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___391_2648 ->
                                               mlog
                                                 (fun uu____2653  ->
                                                    let uu____2654 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2654)
                                                 (fun uu____2656  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2666 =
      let uu____2669 = cur_goal ()  in
      bind uu____2669
        (fun goal  ->
           let uu____2675 =
             let uu____2684 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____2684 t  in
           bind uu____2675
             (fun uu____2695  ->
                match uu____2695 with
                | (uu____2704,typ,uu____2706) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2666
  
let (add_irrelevant_goal :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        FStar_Options.optionstate -> Prims.string -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          fun label1  ->
            let uu____2740 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____2740 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2751  ->
    let uu____2754 = cur_goal ()  in
    bind uu____2754
      (fun goal  ->
         let uu____2760 =
           let uu____2761 = FStar_Tactics_Types.goal_env goal  in
           let uu____2762 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2761 uu____2762  in
         if uu____2760
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2766 =
              let uu____2767 = FStar_Tactics_Types.goal_env goal  in
              let uu____2768 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2767 uu____2768  in
            fail1 "Not a trivial goal: %s" uu____2766))
  
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
             let uu____2817 =
               try
                 (fun uu___397_2840  ->
                    match () with
                    | () ->
                        let uu____2851 =
                          let uu____2860 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2860
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2851) ()
               with | uu___396_2870 -> fail "divide: not enough goals"  in
             bind uu____2817
               (fun uu____2906  ->
                  match uu____2906 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___393_2932 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___393_2932.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___393_2932.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___393_2932.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___393_2932.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___393_2932.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___393_2932.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___393_2932.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___393_2932.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___393_2932.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___393_2932.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___393_2932.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2933 = set lp  in
                      bind uu____2933
                        (fun uu____2941  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___394_2957 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___394_2957.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___394_2957.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___394_2957.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___394_2957.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___394_2957.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___394_2957.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___394_2957.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___394_2957.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___394_2957.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___394_2957.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___394_2957.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2958 = set rp  in
                                     bind uu____2958
                                       (fun uu____2966  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___395_2982 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___395_2982.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___395_2982.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2983 = set p'
                                                       in
                                                    bind uu____2983
                                                      (fun uu____2991  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2997 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3018 = divide FStar_BigInt.one f idtac  in
    bind uu____3018
      (fun uu____3031  -> match uu____3031 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3068::uu____3069 ->
             let uu____3072 =
               let uu____3081 = map tau  in
               divide FStar_BigInt.one tau uu____3081  in
             bind uu____3072
               (fun uu____3099  ->
                  match uu____3099 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3140 =
        bind t1
          (fun uu____3145  ->
             let uu____3146 = map t2  in
             bind uu____3146 (fun uu____3154  -> ret ()))
         in
      focus uu____3140
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3163  ->
    let uu____3166 =
      let uu____3169 = cur_goal ()  in
      bind uu____3169
        (fun goal  ->
           let uu____3178 =
             let uu____3185 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3185  in
           match uu____3178 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3194 =
                 let uu____3195 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3195  in
               if uu____3194
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3200 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3200 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3214 = new_uvar "intro" env' typ'  in
                  bind uu____3214
                    (fun uu____3230  ->
                       match uu____3230 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3254 = set_solution goal sol  in
                           bind uu____3254
                             (fun uu____3260  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3262 =
                                  let uu____3265 = bnorm_goal g  in
                                  replace_cur uu____3265  in
                                bind uu____3262 (fun uu____3267  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3272 =
                 let uu____3273 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3274 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3273 uu____3274  in
               fail1 "goal is not an arrow (%s)" uu____3272)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3166
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3289  ->
    let uu____3296 = cur_goal ()  in
    bind uu____3296
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3313 =
            let uu____3320 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3320  in
          match uu____3313 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3333 =
                let uu____3334 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3334  in
              if uu____3333
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3347 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3347
                    in
                 let bs =
                   let uu____3357 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3357; b]  in
                 let env' =
                   let uu____3383 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3383 bs  in
                 let uu____3384 =
                   let uu____3391 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3391  in
                 bind uu____3384
                   (fun uu____3410  ->
                      match uu____3410 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3424 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3427 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3424
                              FStar_Parser_Const.effect_Tot_lid uu____3427 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3445 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3445 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3467 =
                                   let uu____3468 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3468.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3467
                                  in
                               let uu____3481 = set_solution goal tm  in
                               bind uu____3481
                                 (fun uu____3490  ->
                                    let uu____3491 =
                                      let uu____3494 =
                                        bnorm_goal
                                          (let uu___398_3497 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___398_3497.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___398_3497.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___398_3497.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___398_3497.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____3494  in
                                    bind uu____3491
                                      (fun uu____3504  ->
                                         let uu____3505 =
                                           let uu____3510 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3510, b)  in
                                         ret uu____3505)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3519 =
                let uu____3520 = FStar_Tactics_Types.goal_env goal  in
                let uu____3521 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3520 uu____3521  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3519))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3539 = cur_goal ()  in
    bind uu____3539
      (fun goal  ->
         mlog
           (fun uu____3546  ->
              let uu____3547 =
                let uu____3548 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3548  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3547)
           (fun uu____3553  ->
              let steps =
                let uu____3557 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3557
                 in
              let t =
                let uu____3561 = FStar_Tactics_Types.goal_env goal  in
                let uu____3562 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3561 uu____3562  in
              let uu____3563 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3563))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3587 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____3595 -> g.FStar_Tactics_Types.opts
                 | uu____3598 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____3603  ->
                    let uu____3604 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3604)
                 (fun uu____3607  ->
                    let uu____3608 = __tc_lax e t  in
                    bind uu____3608
                      (fun uu____3629  ->
                         match uu____3629 with
                         | (t1,uu____3639,uu____3640) ->
                             let steps =
                               let uu____3644 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3644
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____3650  ->
                                  let uu____3651 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3651)
                               (fun uu____3653  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3587
  
let (refine_intro : unit -> unit tac) =
  fun uu____3664  ->
    let uu____3667 =
      let uu____3670 = cur_goal ()  in
      bind uu____3670
        (fun g  ->
           let uu____3677 =
             let uu____3688 = FStar_Tactics_Types.goal_env g  in
             let uu____3689 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3688 uu____3689
              in
           match uu____3677 with
           | (uu____3692,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3717 =
                 let uu____3722 =
                   let uu____3727 =
                     let uu____3728 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3728]  in
                   FStar_Syntax_Subst.open_term uu____3727 phi  in
                 match uu____3722 with
                 | (bvs,phi1) ->
                     let uu____3753 =
                       let uu____3754 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3754  in
                     (uu____3753, phi1)
                  in
               (match uu____3717 with
                | (bv1,phi1) ->
                    let uu____3773 =
                      let uu____3776 = FStar_Tactics_Types.goal_env g  in
                      let uu____3777 =
                        let uu____3778 =
                          let uu____3781 =
                            let uu____3782 =
                              let uu____3789 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3789)  in
                            FStar_Syntax_Syntax.NT uu____3782  in
                          [uu____3781]  in
                        FStar_Syntax_Subst.subst uu____3778 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3776
                        uu____3777 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____3773
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3797  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3667
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3816 = cur_goal ()  in
      bind uu____3816
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3824 = FStar_Tactics_Types.goal_env goal  in
               let uu____3825 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3824 uu____3825
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3827 = __tc env t  in
           bind uu____3827
             (fun uu____3846  ->
                match uu____3846 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3861  ->
                         let uu____3862 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3863 =
                           let uu____3864 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3864
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3862 uu____3863)
                      (fun uu____3867  ->
                         let uu____3868 =
                           let uu____3871 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3871 guard  in
                         bind uu____3868
                           (fun uu____3873  ->
                              mlog
                                (fun uu____3877  ->
                                   let uu____3878 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3879 =
                                     let uu____3880 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3880
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3878 uu____3879)
                                (fun uu____3883  ->
                                   let uu____3884 =
                                     let uu____3887 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3888 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3887 typ uu____3888  in
                                   bind uu____3884
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3894 =
                                             let uu____3895 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3895 t1  in
                                           let uu____3896 =
                                             let uu____3897 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3897 typ  in
                                           let uu____3898 =
                                             let uu____3899 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3900 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3899 uu____3900  in
                                           let uu____3901 =
                                             let uu____3902 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3903 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3902 uu____3903  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3894 uu____3896 uu____3898
                                             uu____3901)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3923 =
          mlog
            (fun uu____3928  ->
               let uu____3929 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3929)
            (fun uu____3932  ->
               let uu____3933 =
                 let uu____3940 = __exact_now set_expected_typ1 tm  in
                 catch uu____3940  in
               bind uu____3933
                 (fun uu___353_3949  ->
                    match uu___353_3949 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3960  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3963  ->
                             let uu____3964 =
                               let uu____3971 =
                                 let uu____3974 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3974
                                   (fun uu____3979  ->
                                      let uu____3980 = refine_intro ()  in
                                      bind uu____3980
                                        (fun uu____3984  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3971  in
                             bind uu____3964
                               (fun uu___352_3991  ->
                                  match uu___352_3991 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4000  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4002  -> ret ())
                                  | FStar_Util.Inl uu____4003 ->
                                      mlog
                                        (fun uu____4005  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4007  -> fail e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3923
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4057 = f x  in
          bind uu____4057
            (fun y  ->
               let uu____4065 = mapM f xs  in
               bind uu____4065 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4136 = do_unify e ty1 ty2  in
          bind uu____4136
            (fun uu___354_4148  ->
               if uu___354_4148
               then ret acc
               else
                 (let uu____4167 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4167 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4188 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4189 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4188
                        uu____4189
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4204 =
                        let uu____4205 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4205  in
                      if uu____4204
                      then fail "Codomain is effectful"
                      else
                        (let uu____4225 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4225
                           (fun uu____4251  ->
                              match uu____4251 with
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
      let uu____4337 =
        mlog
          (fun uu____4342  ->
             let uu____4343 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4343)
          (fun uu____4346  ->
             let uu____4347 = cur_goal ()  in
             bind uu____4347
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4355 = __tc e tm  in
                  bind uu____4355
                    (fun uu____4376  ->
                       match uu____4376 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4389 =
                             let uu____4400 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4400  in
                           bind uu____4389
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4443  ->
                                       fun w  ->
                                         match uu____4443 with
                                         | (uvt,q,uu____4461) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4493 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4510  ->
                                       fun s  ->
                                         match uu____4510 with
                                         | (uu____4522,uu____4523,uv) ->
                                             let uu____4525 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4525) uvs uu____4493
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4534 = solve' goal w  in
                                bind uu____4534
                                  (fun uu____4539  ->
                                     let uu____4540 =
                                       mapM
                                         (fun uu____4557  ->
                                            match uu____4557 with
                                            | (uvt,q,uv) ->
                                                let uu____4569 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4569 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4574 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4575 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4575
                                                     then ret ()
                                                     else
                                                       (let uu____4579 =
                                                          let uu____4582 =
                                                            bnorm_goal
                                                              (let uu___399_4585
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___399_4585.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___399_4585.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___399_4585.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____4582]  in
                                                        add_goals uu____4579)))
                                         uvs
                                        in
                                     bind uu____4540
                                       (fun uu____4589  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4337
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4614 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4614
    then
      let uu____4621 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4636 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4689 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4621 with
      | (pre,post) ->
          let post1 =
            let uu____4721 =
              let uu____4732 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4732]  in
            FStar_Syntax_Util.mk_app post uu____4721  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4762 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4762
       then
         let uu____4769 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4769
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4802 =
      let uu____4805 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4812  ->
                  let uu____4813 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4813)
               (fun uu____4817  ->
                  let is_unit_t t =
                    let uu____4824 =
                      let uu____4825 = FStar_Syntax_Subst.compress t  in
                      uu____4825.FStar_Syntax_Syntax.n  in
                    match uu____4824 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4829 -> false  in
                  let uu____4830 = cur_goal ()  in
                  bind uu____4830
                    (fun goal  ->
                       let uu____4836 =
                         let uu____4845 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4845 tm  in
                       bind uu____4836
                         (fun uu____4860  ->
                            match uu____4860 with
                            | (tm1,t,guard) ->
                                let uu____4872 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4872 with
                                 | (bs,comp) ->
                                     let uu____4905 = lemma_or_sq comp  in
                                     (match uu____4905 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4924 =
                                            FStar_List.fold_left
                                              (fun uu____4972  ->
                                                 fun uu____4973  ->
                                                   match (uu____4972,
                                                           uu____4973)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5086 =
                                                         is_unit_t b_t  in
                                                       if uu____5086
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5124 =
                                                            let uu____5137 =
                                                              let uu____5138
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5138.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5141 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5137
                                                              uu____5141 b_t
                                                             in
                                                          match uu____5124
                                                          with
                                                          | (u,uu____5159,g_u)
                                                              ->
                                                              let uu____5173
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5173,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4924 with
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
                                               let uu____5252 =
                                                 let uu____5255 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5256 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5257 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5255
                                                   uu____5256 uu____5257
                                                  in
                                               bind uu____5252
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5265 =
                                                        let uu____5266 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5266 tm1
                                                         in
                                                      let uu____5267 =
                                                        let uu____5268 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5269 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5268
                                                          uu____5269
                                                         in
                                                      let uu____5270 =
                                                        let uu____5271 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5272 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5271
                                                          uu____5272
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5265 uu____5267
                                                        uu____5270
                                                    else
                                                      (let uu____5274 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5274
                                                         (fun uu____5279  ->
                                                            let uu____5280 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5280
                                                              (fun uu____5288
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5313
                                                                    =
                                                                    let uu____5316
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5316
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5313
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
                                                                    let uu____5351
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5351)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5367
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5367
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5385)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5411)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5428
                                                                    -> false)
                                                                    in
                                                                 let uu____5429
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
                                                                    let uu____5459
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5459
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5481)
                                                                    ->
                                                                    let uu____5506
                                                                    =
                                                                    let uu____5507
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5507.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5506
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5515)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___400_5535
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___400_5535.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___400_5535.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___400_5535.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___400_5535.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5538
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5544
                                                                     ->
                                                                    let uu____5545
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5546
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5545
                                                                    uu____5546)
                                                                    (fun
                                                                    uu____5551
                                                                     ->
                                                                    let env =
                                                                    let uu___401_5553
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___401_5553.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5555
                                                                    =
                                                                    let uu____5558
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5559
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5560
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5559
                                                                    uu____5560
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5562
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5558
                                                                    uu____5562
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5555
                                                                    (fun
                                                                    uu____5566
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5429
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
                                                                    let uu____5628
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5628
                                                                    then
                                                                    let uu____5631
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5631
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
                                                                    let uu____5645
                                                                    =
                                                                    let uu____5646
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5646
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5645)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5647
                                                                    =
                                                                    let uu____5650
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5650
                                                                    guard  in
                                                                    bind
                                                                    uu____5647
                                                                    (fun
                                                                    uu____5653
                                                                     ->
                                                                    let uu____5654
                                                                    =
                                                                    let uu____5657
                                                                    =
                                                                    let uu____5658
                                                                    =
                                                                    let uu____5659
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5660
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5659
                                                                    uu____5660
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5658
                                                                     in
                                                                    if
                                                                    uu____5657
                                                                    then
                                                                    let uu____5663
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5663
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5654
                                                                    (fun
                                                                    uu____5666
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4805  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4802
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5688 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5688 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5698::(e1,uu____5700)::(e2,uu____5702)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5763 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5787 = destruct_eq' typ  in
    match uu____5787 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5817 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5817 with
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
        let uu____5879 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5879 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5927 = aux e'  in
               FStar_Util.map_opt uu____5927
                 (fun uu____5951  ->
                    match uu____5951 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5972 = aux e  in
      FStar_Util.map_opt uu____5972
        (fun uu____5996  ->
           match uu____5996 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____6063 =
            let uu____6072 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6072  in
          FStar_Util.map_opt uu____6063
            (fun uu____6087  ->
               match uu____6087 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___402_6106 = bv  in
                     let uu____6107 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___402_6106.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___402_6106.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6107
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___403_6115 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6116 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6125 =
                       let uu____6128 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6128  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___403_6115.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6116;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6125;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___403_6115.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___403_6115.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___403_6115.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___404_6129 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___404_6129.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___404_6129.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___404_6129.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___404_6129.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6139 =
      let uu____6142 = cur_goal ()  in
      bind uu____6142
        (fun goal  ->
           let uu____6150 = h  in
           match uu____6150 with
           | (bv,uu____6154) ->
               mlog
                 (fun uu____6162  ->
                    let uu____6163 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6164 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6163
                      uu____6164)
                 (fun uu____6167  ->
                    let uu____6168 =
                      let uu____6177 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6177  in
                    match uu____6168 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6198 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6198 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6213 =
                               let uu____6214 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6214.FStar_Syntax_Syntax.n  in
                             (match uu____6213 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___405_6231 = bv1  in
                                    let uu____6232 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___405_6231.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___405_6231.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6232
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___406_6240 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6241 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6250 =
                                      let uu____6253 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6253
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___406_6240.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6241;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6250;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___406_6240.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___406_6240.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___406_6240.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___407_6256 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___407_6256.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___407_6256.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___407_6256.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___407_6256.FStar_Tactics_Types.label)
                                     })
                              | uu____6257 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6258 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6139
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6283 =
        let uu____6286 = cur_goal ()  in
        bind uu____6286
          (fun goal  ->
             let uu____6297 = b  in
             match uu____6297 with
             | (bv,uu____6301) ->
                 let bv' =
                   let uu____6307 =
                     let uu___408_6308 = bv  in
                     let uu____6309 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6309;
                       FStar_Syntax_Syntax.index =
                         (uu___408_6308.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___408_6308.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6307  in
                 let s1 =
                   let uu____6313 =
                     let uu____6314 =
                       let uu____6321 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6321)  in
                     FStar_Syntax_Syntax.NT uu____6314  in
                   [uu____6313]  in
                 let uu____6326 = subst_goal bv bv' s1 goal  in
                 (match uu____6326 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6283
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6345 =
      let uu____6348 = cur_goal ()  in
      bind uu____6348
        (fun goal  ->
           let uu____6357 = b  in
           match uu____6357 with
           | (bv,uu____6361) ->
               let uu____6366 =
                 let uu____6375 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6375  in
               (match uu____6366 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6396 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6396 with
                     | (ty,u) ->
                         let uu____6405 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6405
                           (fun uu____6423  ->
                              match uu____6423 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___409_6433 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___409_6433.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___409_6433.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6437 =
                                      let uu____6438 =
                                        let uu____6445 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6445)  in
                                      FStar_Syntax_Syntax.NT uu____6438  in
                                    [uu____6437]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___410_6457 = b1  in
                                         let uu____6458 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___410_6457.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___410_6457.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6458
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6465  ->
                                       let new_goal =
                                         let uu____6467 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6468 =
                                           let uu____6469 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6469
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6467 uu____6468
                                          in
                                       let uu____6470 = add_goals [new_goal]
                                          in
                                       bind uu____6470
                                         (fun uu____6475  ->
                                            let uu____6476 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6476
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6345
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6499 =
        let uu____6502 = cur_goal ()  in
        bind uu____6502
          (fun goal  ->
             let uu____6511 = b  in
             match uu____6511 with
             | (bv,uu____6515) ->
                 let uu____6520 =
                   let uu____6529 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6529  in
                 (match uu____6520 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6553 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6553
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___411_6558 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___411_6558.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___411_6558.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6560 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6560))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6499
  
let (revert : unit -> unit tac) =
  fun uu____6571  ->
    let uu____6574 = cur_goal ()  in
    bind uu____6574
      (fun goal  ->
         let uu____6580 =
           let uu____6587 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6587  in
         match uu____6580 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6603 =
                 let uu____6606 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6606  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6603
                in
             let uu____6621 = new_uvar "revert" env' typ'  in
             bind uu____6621
               (fun uu____6636  ->
                  match uu____6636 with
                  | (r,u_r) ->
                      let uu____6645 =
                        let uu____6648 =
                          let uu____6649 =
                            let uu____6650 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6650.FStar_Syntax_Syntax.pos  in
                          let uu____6653 =
                            let uu____6658 =
                              let uu____6659 =
                                let uu____6668 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6668  in
                              [uu____6659]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6658  in
                          uu____6653 FStar_Pervasives_Native.None uu____6649
                           in
                        set_solution goal uu____6648  in
                      bind uu____6645
                        (fun uu____6689  ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label
                              in
                           replace_cur g)))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____6701 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6701
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6716 = cur_goal ()  in
    bind uu____6716
      (fun goal  ->
         mlog
           (fun uu____6724  ->
              let uu____6725 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6726 =
                let uu____6727 =
                  let uu____6728 =
                    let uu____6737 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6737  in
                  FStar_All.pipe_right uu____6728 FStar_List.length  in
                FStar_All.pipe_right uu____6727 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6725 uu____6726)
           (fun uu____6754  ->
              let uu____6755 =
                let uu____6764 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6764  in
              match uu____6755 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6803 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6803
                        then
                          let uu____6806 =
                            let uu____6807 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6807
                             in
                          fail uu____6806
                        else check1 bvs2
                     in
                  let uu____6809 =
                    let uu____6810 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6810  in
                  if uu____6809
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6814 = check1 bvs  in
                     bind uu____6814
                       (fun uu____6820  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6822 =
                            let uu____6829 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6829  in
                          bind uu____6822
                            (fun uu____6838  ->
                               match uu____6838 with
                               | (ut,uvar_ut) ->
                                   let uu____6847 = set_solution goal ut  in
                                   bind uu____6847
                                     (fun uu____6852  ->
                                        let uu____6853 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____6853))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6860  ->
    let uu____6863 = cur_goal ()  in
    bind uu____6863
      (fun goal  ->
         let uu____6869 =
           let uu____6876 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6876  in
         match uu____6869 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6884) ->
             let uu____6889 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6889)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6899 = cur_goal ()  in
    bind uu____6899
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6909 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6909  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6912  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6922 = cur_goal ()  in
    bind uu____6922
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6932 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6932  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6935  -> add_goals [g']))
  
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
            let uu____6975 = FStar_Syntax_Subst.compress t  in
            uu____6975.FStar_Syntax_Syntax.n  in
          let uu____6978 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___415_6984 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___415_6984.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___415_6984.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6978
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7000 =
                   let uu____7001 = FStar_Syntax_Subst.compress t1  in
                   uu____7001.FStar_Syntax_Syntax.n  in
                 match uu____7000 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____7032 = ff hd1  in
                     bind uu____7032
                       (fun hd2  ->
                          let fa uu____7058 =
                            match uu____7058 with
                            | (a,q) ->
                                let uu____7079 = ff a  in
                                bind uu____7079 (fun a1  -> ret (a1, q))
                             in
                          let uu____7098 = mapM fa args  in
                          bind uu____7098
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7180 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7180 with
                      | (bs1,t') ->
                          let uu____7189 =
                            let uu____7192 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7192 t'  in
                          bind uu____7189
                            (fun t''  ->
                               let uu____7196 =
                                 let uu____7197 =
                                   let uu____7216 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7225 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7216, uu____7225, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7197  in
                               ret uu____7196))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7300 = ff hd1  in
                     bind uu____7300
                       (fun hd2  ->
                          let ffb br =
                            let uu____7315 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7315 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7347 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7347  in
                                let uu____7348 = ff1 e  in
                                bind uu____7348
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7363 = mapM ffb brs  in
                          bind uu____7363
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7407;
                          FStar_Syntax_Syntax.lbtyp = uu____7408;
                          FStar_Syntax_Syntax.lbeff = uu____7409;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7411;
                          FStar_Syntax_Syntax.lbpos = uu____7412;_}::[]),e)
                     ->
                     let lb =
                       let uu____7437 =
                         let uu____7438 = FStar_Syntax_Subst.compress t1  in
                         uu____7438.FStar_Syntax_Syntax.n  in
                       match uu____7437 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7442) -> lb
                       | uu____7455 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7464 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7464
                         (fun def1  ->
                            ret
                              (let uu___412_7470 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___412_7470.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___412_7470.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___412_7470.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___412_7470.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___412_7470.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___412_7470.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7471 = fflb lb  in
                     bind uu____7471
                       (fun lb1  ->
                          let uu____7481 =
                            let uu____7486 =
                              let uu____7487 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7487]  in
                            FStar_Syntax_Subst.open_term uu____7486 e  in
                          match uu____7481 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7517 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7517  in
                              let uu____7518 = ff1 e1  in
                              bind uu____7518
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7559 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7559
                         (fun def  ->
                            ret
                              (let uu___413_7565 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___413_7565.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___413_7565.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___413_7565.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___413_7565.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___413_7565.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___413_7565.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7566 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7566 with
                      | (lbs1,e1) ->
                          let uu____7581 = mapM fflb lbs1  in
                          bind uu____7581
                            (fun lbs2  ->
                               let uu____7593 = ff e1  in
                               bind uu____7593
                                 (fun e2  ->
                                    let uu____7601 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7601 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7669 = ff t2  in
                     bind uu____7669
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7700 = ff t2  in
                     bind uu____7700
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7707 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___414_7714 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___414_7714.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___414_7714.FStar_Syntax_Syntax.vars)
                      }  in
                    if d = FStar_Tactics_Types.BottomUp
                    then f env t'
                    else ret t'))
  
let (pointwise_rec :
  FStar_Tactics_Types.proofstate ->
    unit tac ->
      FStar_Options.optionstate ->
        Prims.string ->
          FStar_TypeChecker_Env.env ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ps  ->
    fun tau  ->
      fun opts  ->
        fun label1  ->
          fun env  ->
            fun t  ->
              let uu____7756 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___416_7765 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___416_7765.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___416_7765.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___416_7765.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___416_7765.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___416_7765.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___416_7765.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___416_7765.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___416_7765.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___416_7765.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___416_7765.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___416_7765.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___416_7765.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___416_7765.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___416_7765.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___416_7765.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___416_7765.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___416_7765.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___416_7765.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___416_7765.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___416_7765.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___416_7765.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___416_7765.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___416_7765.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___416_7765.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___416_7765.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___416_7765.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___416_7765.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___416_7765.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___416_7765.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___416_7765.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___416_7765.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___416_7765.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___416_7765.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___416_7765.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___416_7765.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___416_7765.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___416_7765.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___416_7765.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___416_7765.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___416_7765.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___416_7765.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___416_7765.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____7756 with
              | (t1,lcomp,g) ->
                  let uu____7771 =
                    (let uu____7774 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____7774) ||
                      (let uu____7776 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____7776)
                     in
                  if uu____7771
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____7784 = new_uvar "pointwise_rec" env typ  in
                       bind uu____7784
                         (fun uu____7800  ->
                            match uu____7800 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____7813  ->
                                      let uu____7814 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____7815 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____7814 uu____7815);
                                 (let uu____7816 =
                                    let uu____7819 =
                                      let uu____7820 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____7820 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____7819
                                      opts label1
                                     in
                                  bind uu____7816
                                    (fun uu____7823  ->
                                       let uu____7824 =
                                         bind tau
                                           (fun uu____7830  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____7836  ->
                                                   let uu____7837 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____7838 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____7837 uu____7838);
                                              ret ut1)
                                          in
                                       focus uu____7824))))
                        in
                     let uu____7839 = catch rewrite_eq  in
                     bind uu____7839
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
          let uu____8037 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____8037
            (fun t1  ->
               let uu____8045 =
                 f env
                   (let uu___419_8054 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___419_8054.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___419_8054.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____8045
                 (fun uu____8070  ->
                    match uu____8070 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____8093 =
                               let uu____8094 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____8094.FStar_Syntax_Syntax.n  in
                             match uu____8093 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8131 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8131
                                   (fun uu____8156  ->
                                      match uu____8156 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8172 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8172
                                            (fun uu____8199  ->
                                               match uu____8199 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___417_8229 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___417_8229.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___417_8229.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8271 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8271 with
                                  | (bs1,t') ->
                                      let uu____8286 =
                                        let uu____8293 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8293 ctrl1 t'
                                         in
                                      bind uu____8286
                                        (fun uu____8311  ->
                                           match uu____8311 with
                                           | (t'',ctrl2) ->
                                               let uu____8326 =
                                                 let uu____8333 =
                                                   let uu___418_8336 = t4  in
                                                   let uu____8339 =
                                                     let uu____8340 =
                                                       let uu____8359 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8368 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8359,
                                                         uu____8368, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8340
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8339;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___418_8336.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___418_8336.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8333, ctrl2)  in
                                               ret uu____8326))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8421 -> ret (t3, ctrl1))))

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
              let uu____8468 = ctrl_tac_fold f env ctrl t  in
              bind uu____8468
                (fun uu____8492  ->
                   match uu____8492 with
                   | (t1,ctrl1) ->
                       let uu____8507 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8507
                         (fun uu____8534  ->
                            match uu____8534 with
                            | (ts2,ctrl2) -> ret (((t1, q) :: ts2), ctrl2)))

let (rewrite_rec :
  FStar_Tactics_Types.proofstate ->
    (FStar_Syntax_Syntax.term -> rewrite_result ctrl_tac) ->
      unit tac ->
        FStar_Options.optionstate ->
          Prims.string ->
            FStar_TypeChecker_Env.env ->
              FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term ctrl_tac)
  =
  fun ps  ->
    fun ctrl  ->
      fun rewriter  ->
        fun opts  ->
          fun label1  ->
            fun env  ->
              fun t  ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let uu____8623 =
                  let uu____8630 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____8630
                    (fun uu____8639  ->
                       let uu____8640 = ctrl t1  in
                       bind uu____8640
                         (fun res  ->
                            let uu____8663 = trivial ()  in
                            bind uu____8663 (fun uu____8671  -> ret res)))
                   in
                bind uu____8623
                  (fun uu____8687  ->
                     match uu____8687 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____8711 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___420_8720 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___420_8720.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___420_8720.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___420_8720.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___420_8720.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___420_8720.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___420_8720.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___420_8720.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___420_8720.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___420_8720.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___420_8720.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___420_8720.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___420_8720.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___420_8720.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___420_8720.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___420_8720.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___420_8720.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___420_8720.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___420_8720.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___420_8720.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___420_8720.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___420_8720.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___420_8720.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___420_8720.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___420_8720.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___420_8720.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___420_8720.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___420_8720.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___420_8720.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___420_8720.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___420_8720.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___420_8720.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___420_8720.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___420_8720.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___420_8720.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___420_8720.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___420_8720.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___420_8720.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___420_8720.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___420_8720.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___420_8720.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___420_8720.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___420_8720.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____8711 with
                            | (t2,lcomp,g) ->
                                let uu____8730 =
                                  (let uu____8733 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____8733) ||
                                    (let uu____8735 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____8735)
                                   in
                                if uu____8730
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____8748 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____8748
                                     (fun uu____8768  ->
                                        match uu____8768 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____8785  ->
                                                  let uu____8786 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____8787 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____8786 uu____8787);
                                             (let uu____8788 =
                                                let uu____8791 =
                                                  let uu____8792 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8792 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____8791 opts label1
                                                 in
                                              bind uu____8788
                                                (fun uu____8799  ->
                                                   let uu____8800 =
                                                     bind rewriter
                                                       (fun uu____8814  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____8820 
                                                               ->
                                                               let uu____8821
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____8822
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____8821
                                                                 uu____8822);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____8800)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8863 =
        bind get
          (fun ps  ->
             let uu____8873 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8873 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8910  ->
                       let uu____8911 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8911);
                  bind dismiss_all
                    (fun uu____8914  ->
                       let uu____8915 =
                         let uu____8922 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____8922
                           keepGoing gt1
                          in
                       bind uu____8915
                         (fun uu____8934  ->
                            match uu____8934 with
                            | (gt',uu____8942) ->
                                (log ps
                                   (fun uu____8946  ->
                                      let uu____8947 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8947);
                                 (let uu____8948 = push_goals gs  in
                                  bind uu____8948
                                    (fun uu____8953  ->
                                       let uu____8954 =
                                         let uu____8957 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8957]  in
                                       add_goals uu____8954)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8863
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8980 =
        bind get
          (fun ps  ->
             let uu____8990 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8990 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9027  ->
                       let uu____9028 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____9028);
                  bind dismiss_all
                    (fun uu____9031  ->
                       let uu____9032 =
                         let uu____9035 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9035 gt1
                          in
                       bind uu____9032
                         (fun gt'  ->
                            log ps
                              (fun uu____9043  ->
                                 let uu____9044 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____9044);
                            (let uu____9045 = push_goals gs  in
                             bind uu____9045
                               (fun uu____9050  ->
                                  let uu____9051 =
                                    let uu____9054 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____9054]  in
                                  add_goals uu____9051))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8980
  
let (trefl : unit -> unit tac) =
  fun uu____9065  ->
    let uu____9068 =
      let uu____9071 = cur_goal ()  in
      bind uu____9071
        (fun g  ->
           let uu____9089 =
             let uu____9094 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____9094  in
           match uu____9089 with
           | FStar_Pervasives_Native.Some t ->
               let uu____9102 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____9102 with
                | (hd1,args) ->
                    let uu____9141 =
                      let uu____9154 =
                        let uu____9155 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9155.FStar_Syntax_Syntax.n  in
                      (uu____9154, args)  in
                    (match uu____9141 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9169::(l,uu____9171)::(r,uu____9173)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9220 =
                           let uu____9223 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9223 l r  in
                         bind uu____9220
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9230 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9230 l
                                    in
                                 let r1 =
                                   let uu____9232 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9232 r
                                    in
                                 let uu____9233 =
                                   let uu____9236 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9236 l1 r1  in
                                 bind uu____9233
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9242 =
                                           let uu____9243 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9243 l1  in
                                         let uu____9244 =
                                           let uu____9245 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9245 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9242 uu____9244))))
                     | (hd2,uu____9247) ->
                         let uu____9264 =
                           let uu____9265 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9265 t  in
                         fail1 "trefl: not an equality (%s)" uu____9264))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____9068
  
let (dup : unit -> unit tac) =
  fun uu____9278  ->
    let uu____9281 = cur_goal ()  in
    bind uu____9281
      (fun g  ->
         let uu____9287 =
           let uu____9294 = FStar_Tactics_Types.goal_env g  in
           let uu____9295 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9294 uu____9295  in
         bind uu____9287
           (fun uu____9304  ->
              match uu____9304 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___421_9314 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___421_9314.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___421_9314.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___421_9314.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___421_9314.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____9317  ->
                       let uu____9318 =
                         let uu____9321 = FStar_Tactics_Types.goal_env g  in
                         let uu____9322 =
                           let uu____9323 =
                             let uu____9324 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9325 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9324
                               uu____9325
                              in
                           let uu____9326 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9327 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9323 uu____9326 u
                             uu____9327
                            in
                         add_irrelevant_goal "dup equation" uu____9321
                           uu____9322 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____9318
                         (fun uu____9330  ->
                            let uu____9331 = add_goals [g']  in
                            bind uu____9331 (fun uu____9335  -> ret ())))))
  
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
              let uu____9458 = f x y  in
              if uu____9458 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9478 -> (acc, l11, l21)  in
        let uu____9493 = aux [] l1 l2  in
        match uu____9493 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9598 = get_phi g1  in
      match uu____9598 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9604 = get_phi g2  in
          (match uu____9604 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9616 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9616 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9647 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____9647 phi1  in
                    let t2 =
                      let uu____9657 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____9657 phi2  in
                    let uu____9666 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9666
                      (fun uu____9671  ->
                         let uu____9672 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9672
                           (fun uu____9679  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___422_9684 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9685 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___422_9684.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___422_9684.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___422_9684.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___422_9684.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9685;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___422_9684.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___422_9684.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___422_9684.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___422_9684.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___422_9684.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___422_9684.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___422_9684.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___422_9684.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___422_9684.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___422_9684.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___422_9684.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___422_9684.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___422_9684.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___422_9684.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___422_9684.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___422_9684.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___422_9684.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___422_9684.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___422_9684.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___422_9684.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___422_9684.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___422_9684.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___422_9684.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___422_9684.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___422_9684.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___422_9684.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___422_9684.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___422_9684.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___422_9684.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___422_9684.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___422_9684.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___422_9684.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___422_9684.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___422_9684.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___422_9684.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___422_9684.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___422_9684.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9688 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____9688
                                (fun goal  ->
                                   mlog
                                     (fun uu____9697  ->
                                        let uu____9698 =
                                          goal_to_string_verbose g1  in
                                        let uu____9699 =
                                          goal_to_string_verbose g2  in
                                        let uu____9700 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9698 uu____9699 uu____9700)
                                     (fun uu____9702  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9709  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9725 =
               set
                 (let uu___423_9730 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___423_9730.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___423_9730.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___423_9730.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___423_9730.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___423_9730.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___423_9730.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___423_9730.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___423_9730.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___423_9730.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___423_9730.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___423_9730.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___423_9730.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9725
               (fun uu____9733  ->
                  let uu____9734 = join_goals g1 g2  in
                  bind uu____9734 (fun g12  -> add_goals [g12]))
         | uu____9739 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9759 =
      let uu____9766 = cur_goal ()  in
      bind uu____9766
        (fun g  ->
           let uu____9776 =
             let uu____9785 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9785 t  in
           bind uu____9776
             (fun uu____9813  ->
                match uu____9813 with
                | (t1,typ,guard) ->
                    let uu____9829 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9829 with
                     | (hd1,args) ->
                         let uu____9878 =
                           let uu____9893 =
                             let uu____9894 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9894.FStar_Syntax_Syntax.n  in
                           (uu____9893, args)  in
                         (match uu____9878 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9915)::(q,uu____9917)::[]) when
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
                                let uu____9971 =
                                  let uu____9972 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9972
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9971
                                 in
                              let g2 =
                                let uu____9974 =
                                  let uu____9975 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9975
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9974
                                 in
                              bind __dismiss
                                (fun uu____9982  ->
                                   let uu____9983 = add_goals [g1; g2]  in
                                   bind uu____9983
                                     (fun uu____9992  ->
                                        let uu____9993 =
                                          let uu____9998 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9999 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9998, uu____9999)  in
                                        ret uu____9993))
                          | uu____10004 ->
                              let uu____10019 =
                                let uu____10020 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____10020 typ  in
                              fail1 "Not a disjunction: %s" uu____10019))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9759
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____10050 =
      let uu____10053 = cur_goal ()  in
      bind uu____10053
        (fun g  ->
           FStar_Options.push ();
           (let uu____10066 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____10066);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___424_10073 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___424_10073.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___424_10073.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___424_10073.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___424_10073.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____10050
  
let (top_env : unit -> env tac) =
  fun uu____10085  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10098  ->
    let uu____10101 = cur_goal ()  in
    bind uu____10101
      (fun g  ->
         let uu____10107 =
           (FStar_Options.lax ()) ||
             (let uu____10109 = FStar_Tactics_Types.goal_env g  in
              uu____10109.FStar_TypeChecker_Env.lax)
            in
         ret uu____10107)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10124 =
        mlog
          (fun uu____10129  ->
             let uu____10130 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10130)
          (fun uu____10133  ->
             let uu____10134 = cur_goal ()  in
             bind uu____10134
               (fun goal  ->
                  let env =
                    let uu____10142 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10142 ty  in
                  let uu____10143 = __tc_ghost env tm  in
                  bind uu____10143
                    (fun uu____10162  ->
                       match uu____10162 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10176  ->
                                let uu____10177 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10177)
                             (fun uu____10179  ->
                                mlog
                                  (fun uu____10182  ->
                                     let uu____10183 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10183)
                                  (fun uu____10186  ->
                                     let uu____10187 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10187
                                       (fun uu____10191  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10124
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10214 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10220 =
              let uu____10227 =
                let uu____10228 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10228
                 in
              new_uvar "uvar_env.2" env uu____10227  in
            bind uu____10220
              (fun uu____10244  ->
                 match uu____10244 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10214
        (fun typ  ->
           let uu____10256 = new_uvar "uvar_env" env typ  in
           bind uu____10256
             (fun uu____10270  ->
                match uu____10270 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10288 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10307 -> g.FStar_Tactics_Types.opts
             | uu____10310 -> FStar_Options.peek ()  in
           let uu____10313 = FStar_Syntax_Util.head_and_args t  in
           match uu____10313 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10333);
                FStar_Syntax_Syntax.pos = uu____10334;
                FStar_Syntax_Syntax.vars = uu____10335;_},uu____10336)
               ->
               let env1 =
                 let uu___425_10378 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___425_10378.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___425_10378.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___425_10378.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___425_10378.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___425_10378.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___425_10378.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___425_10378.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___425_10378.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___425_10378.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___425_10378.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___425_10378.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___425_10378.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___425_10378.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___425_10378.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___425_10378.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___425_10378.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___425_10378.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___425_10378.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___425_10378.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___425_10378.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___425_10378.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___425_10378.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___425_10378.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___425_10378.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___425_10378.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___425_10378.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___425_10378.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___425_10378.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___425_10378.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___425_10378.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___425_10378.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___425_10378.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___425_10378.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___425_10378.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___425_10378.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___425_10378.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___425_10378.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___425_10378.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___425_10378.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___425_10378.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___425_10378.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___425_10378.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____10380 =
                 let uu____10383 = bnorm_goal g  in [uu____10383]  in
               add_goals uu____10380
           | uu____10384 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10288
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10433 = if b then t2 else ret false  in
             bind uu____10433 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10444 = trytac comp  in
      bind uu____10444
        (fun uu___355_10452  ->
           match uu___355_10452 with
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
        let uu____10478 =
          bind get
            (fun ps  ->
               let uu____10484 = __tc e t1  in
               bind uu____10484
                 (fun uu____10504  ->
                    match uu____10504 with
                    | (t11,ty1,g1) ->
                        let uu____10516 = __tc e t2  in
                        bind uu____10516
                          (fun uu____10536  ->
                             match uu____10536 with
                             | (t21,ty2,g2) ->
                                 let uu____10548 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10548
                                   (fun uu____10553  ->
                                      let uu____10554 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10554
                                        (fun uu____10560  ->
                                           let uu____10561 =
                                             do_unify e ty1 ty2  in
                                           let uu____10564 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10561 uu____10564)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10478
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10597  ->
             let uu____10598 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10598
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
        (fun uu____10619  ->
           let uu____10620 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10620)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10630 =
      mlog
        (fun uu____10635  ->
           let uu____10636 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10636)
        (fun uu____10639  ->
           let uu____10640 = cur_goal ()  in
           bind uu____10640
             (fun g  ->
                let uu____10646 =
                  let uu____10655 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10655 ty  in
                bind uu____10646
                  (fun uu____10667  ->
                     match uu____10667 with
                     | (ty1,uu____10677,guard) ->
                         let uu____10679 =
                           let uu____10682 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10682 guard  in
                         bind uu____10679
                           (fun uu____10685  ->
                              let uu____10686 =
                                let uu____10689 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10690 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10689 uu____10690 ty1  in
                              bind uu____10686
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10696 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10696
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10702 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10703 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10702
                                          uu____10703
                                         in
                                      let nty =
                                        let uu____10705 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10705 ty1  in
                                      let uu____10706 =
                                        let uu____10709 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10709 ng nty  in
                                      bind uu____10706
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10715 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10715
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10630
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10778 =
      let uu____10787 = cur_goal ()  in
      bind uu____10787
        (fun g  ->
           let uu____10799 =
             let uu____10808 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10808 s_tm  in
           bind uu____10799
             (fun uu____10826  ->
                match uu____10826 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10844 =
                      let uu____10847 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10847 guard  in
                    bind uu____10844
                      (fun uu____10859  ->
                         let uu____10860 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10860 with
                         | (h,args) ->
                             let uu____10905 =
                               let uu____10912 =
                                 let uu____10913 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10913.FStar_Syntax_Syntax.n  in
                               match uu____10912 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10928;
                                      FStar_Syntax_Syntax.vars = uu____10929;_},us)
                                   -> ret (fv, us)
                               | uu____10939 -> fail "type is not an fv"  in
                             bind uu____10905
                               (fun uu____10959  ->
                                  match uu____10959 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10975 =
                                        let uu____10978 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10978 t_lid
                                         in
                                      (match uu____10975 with
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
                                                  (fun uu____11027  ->
                                                     let uu____11028 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____11028 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____11043 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____11071
                                                                  =
                                                                  let uu____11074
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____11074
                                                                    c_lid
                                                                   in
                                                                match uu____11071
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
                                                                    uu____11144
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
                                                                    let uu____11149
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11149
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11172
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11172
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11215
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11215
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11288
                                                                    =
                                                                    let uu____11289
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11289
                                                                     in
                                                                    failwhen
                                                                    uu____11288
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11306
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
                                                                    uu___356_11322
                                                                    =
                                                                    match uu___356_11322
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11325)
                                                                    -> true
                                                                    | 
                                                                    uu____11326
                                                                    -> false
                                                                     in
                                                                    let uu____11329
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11329
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
                                                                    uu____11462
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
                                                                    uu____11524
                                                                     ->
                                                                    match uu____11524
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11544),
                                                                    (t,uu____11546))
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
                                                                    uu____11614
                                                                     ->
                                                                    match uu____11614
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11640),
                                                                    (t,uu____11642))
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
                                                                    uu____11697
                                                                     ->
                                                                    match uu____11697
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
                                                                    let uu____11747
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___426_11764
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___426_11764.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____11747
                                                                    with
                                                                    | 
                                                                    (uu____11777,uu____11778,uu____11779,pat_t,uu____11781,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11788
                                                                    =
                                                                    let uu____11789
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11789
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11788
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11793
                                                                    =
                                                                    let uu____11802
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11802]
                                                                     in
                                                                    let uu____11821
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11793
                                                                    uu____11821
                                                                     in
                                                                    let nty =
                                                                    let uu____11827
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11827
                                                                     in
                                                                    let uu____11830
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11830
                                                                    (fun
                                                                    uu____11859
                                                                     ->
                                                                    match uu____11859
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label
                                                                     in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____11885
                                                                    =
                                                                    let uu____11896
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11896]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11885
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11932
                                                                    =
                                                                    let uu____11943
                                                                    =
                                                                    let uu____11948
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11948)
                                                                     in
                                                                    (g', br,
                                                                    uu____11943)
                                                                     in
                                                                    ret
                                                                    uu____11932))))))
                                                                    | 
                                                                    uu____11969
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____11043
                                                           (fun goal_brs  ->
                                                              let uu____12018
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____12018
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
                                                                  let uu____12091
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12091
                                                                    (
                                                                    fun
                                                                    uu____12102
                                                                     ->
                                                                    let uu____12103
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12103
                                                                    (fun
                                                                    uu____12113
                                                                     ->
                                                                    ret infos))))
                                            | uu____12120 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10778
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12165::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12193 = init xs  in x :: uu____12193
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12205 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12214) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12279 = last args  in
          (match uu____12279 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12309 =
                 let uu____12310 =
                   let uu____12315 =
                     let uu____12316 =
                       let uu____12321 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12321  in
                     uu____12316 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12315, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12310  in
               FStar_All.pipe_left ret uu____12309)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12334,uu____12335) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12387 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12387 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12428 =
                      let uu____12429 =
                        let uu____12434 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12434)  in
                      FStar_Reflection_Data.Tv_Abs uu____12429  in
                    FStar_All.pipe_left ret uu____12428))
      | FStar_Syntax_Syntax.Tm_type uu____12437 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12461 ->
          let uu____12476 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12476 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12506 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12506 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12559 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12571 =
            let uu____12572 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12572  in
          FStar_All.pipe_left ret uu____12571
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12593 =
            let uu____12594 =
              let uu____12599 =
                let uu____12600 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12600  in
              (uu____12599, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12594  in
          FStar_All.pipe_left ret uu____12593
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12634 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12639 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12639 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12692 ->
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
             | FStar_Util.Inr uu____12726 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12730 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12730 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12750 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12754 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12808 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12808
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12827 =
                  let uu____12834 =
                    FStar_List.map
                      (fun uu____12846  ->
                         match uu____12846 with
                         | (p1,uu____12854) -> inspect_pat p1) ps
                     in
                  (fv, uu____12834)  in
                FStar_Reflection_Data.Pat_Cons uu____12827
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
              (fun uu___357_12948  ->
                 match uu___357_12948 with
                 | (pat,uu____12970,t5) ->
                     let uu____12988 = inspect_pat pat  in (uu____12988, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12997 ->
          ((let uu____12999 =
              let uu____13004 =
                let uu____13005 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____13006 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____13005 uu____13006
                 in
              (FStar_Errors.Warning_CantInspect, uu____13004)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12999);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12205
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____13019 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____13019
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____13023 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____13023
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____13027 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____13027
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____13034 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____13034
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____13059 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____13059
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____13076 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____13076
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13095 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13095
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13099 =
          let uu____13100 =
            let uu____13107 =
              let uu____13108 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13108  in
            FStar_Syntax_Syntax.mk uu____13107  in
          uu____13100 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13099
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13116 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13116
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13125 =
          let uu____13126 =
            let uu____13133 =
              let uu____13134 =
                let uu____13147 =
                  let uu____13150 =
                    let uu____13151 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13151]  in
                  FStar_Syntax_Subst.close uu____13150 t2  in
                ((false, [lb]), uu____13147)  in
              FStar_Syntax_Syntax.Tm_let uu____13134  in
            FStar_Syntax_Syntax.mk uu____13133  in
          uu____13126 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13125
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13191 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13191 with
         | (lbs,body) ->
             let uu____13206 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13206)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13240 =
                let uu____13241 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13241  in
              FStar_All.pipe_left wrap uu____13240
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13248 =
                let uu____13249 =
                  let uu____13262 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13278 = pack_pat p1  in
                         (uu____13278, false)) ps
                     in
                  (fv, uu____13262)  in
                FStar_Syntax_Syntax.Pat_cons uu____13249  in
              FStar_All.pipe_left wrap uu____13248
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
            (fun uu___358_13324  ->
               match uu___358_13324 with
               | (pat,t1) ->
                   let uu____13341 = pack_pat pat  in
                   (uu____13341, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13389 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13389
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13417 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13417
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13463 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13463
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13502 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13502
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13519 =
        bind get
          (fun ps  ->
             let uu____13525 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13525 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13519
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13554 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___427_13561 = ps  in
                 let uu____13562 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___427_13561.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___427_13561.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___427_13561.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___427_13561.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___427_13561.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___427_13561.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___427_13561.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___427_13561.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___427_13561.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___427_13561.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___427_13561.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___427_13561.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13562
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13554
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13587 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13587 with
      | (u,ctx_uvars,g_u) ->
          let uu____13619 = FStar_List.hd ctx_uvars  in
          (match uu____13619 with
           | (ctx_uvar,uu____13633) ->
               let g =
                 let uu____13635 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13635 false
                   ""
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
        let uu____13655 = goal_of_goal_ty env typ  in
        match uu____13655 with
        | (g,g_u) ->
            let ps =
              let uu____13667 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13668 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13667;
                FStar_Tactics_Types.local_state = uu____13668
              }  in
            let uu____13675 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13675)
  