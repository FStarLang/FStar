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
        (try (fun uu___358_158  -> match () with | () -> run t p) ()
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
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____444)
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____456 = goal_to_string ps goal  in tacprint uu____456
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____468 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____472 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____472))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____481  ->
    match uu____481 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____494 =
          let uu____497 =
            let uu____498 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____498 msg
             in
          let uu____499 =
            let uu____502 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____503 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____503
              else ""  in
            let uu____505 =
              let uu____508 =
                let uu____509 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____509
                then
                  let uu____510 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____510
                else ""  in
              let uu____512 =
                let uu____515 =
                  let uu____516 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____517 =
                    let uu____518 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____518  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____516
                    uu____517
                   in
                let uu____521 =
                  let uu____524 =
                    let uu____525 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____526 =
                      let uu____527 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____527  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____525
                      uu____526
                     in
                  [uu____524]  in
                uu____515 :: uu____521  in
              uu____508 :: uu____512  in
            uu____502 :: uu____505  in
          uu____497 :: uu____499  in
        FStar_String.concat "" uu____494
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____536 =
        let uu____537 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____537  in
      let uu____538 =
        let uu____543 =
          let uu____544 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____544  in
        FStar_Syntax_Print.binders_to_json uu____543  in
      FStar_All.pipe_right uu____536 uu____538  in
    let uu____545 =
      let uu____552 =
        let uu____559 =
          let uu____564 =
            let uu____565 =
              let uu____572 =
                let uu____577 =
                  let uu____578 =
                    let uu____579 = FStar_Tactics_Types.goal_env g  in
                    let uu____580 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____579 uu____580  in
                  FStar_Util.JsonStr uu____578  in
                ("witness", uu____577)  in
              let uu____581 =
                let uu____588 =
                  let uu____593 =
                    let uu____594 =
                      let uu____595 = FStar_Tactics_Types.goal_env g  in
                      let uu____596 = FStar_Tactics_Types.goal_type g  in
                      tts uu____595 uu____596  in
                    FStar_Util.JsonStr uu____594  in
                  ("type", uu____593)  in
                [uu____588]  in
              uu____572 :: uu____581  in
            FStar_Util.JsonAssoc uu____565  in
          ("goal", uu____564)  in
        [uu____559]  in
      ("hyps", g_binders) :: uu____552  in
    FStar_Util.JsonAssoc uu____545
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____629  ->
    match uu____629 with
    | (msg,ps) ->
        let uu____636 =
          let uu____643 =
            let uu____650 =
              let uu____657 =
                let uu____664 =
                  let uu____669 =
                    let uu____670 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____670  in
                  ("goals", uu____669)  in
                let uu____673 =
                  let uu____680 =
                    let uu____685 =
                      let uu____686 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____686  in
                    ("smt-goals", uu____685)  in
                  [uu____680]  in
                uu____664 :: uu____673  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____657
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____650  in
          let uu____709 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____722 =
                let uu____727 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____727)  in
              [uu____722]
            else []  in
          FStar_List.append uu____643 uu____709  in
        FStar_Util.JsonAssoc uu____636
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____757  ->
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
         (let uu____780 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____780 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____798 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____798 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____852 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____852
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____860 . Prims.string -> Prims.string -> 'Auu____860 tac =
  fun msg  ->
    fun x  -> let uu____873 = FStar_Util.format1 msg x  in fail uu____873
  
let fail2 :
  'Auu____882 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____882 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____900 = FStar_Util.format2 msg x y  in fail uu____900
  
let fail3 :
  'Auu____911 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____911 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____934 = FStar_Util.format3 msg x y z  in fail uu____934
  
let fail4 :
  'Auu____947 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____947 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____975 = FStar_Util.format4 msg x y z w  in fail uu____975
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1008 = run t ps  in
         match uu____1008 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___359_1032 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___359_1032.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___359_1032.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___359_1032.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___359_1032.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___359_1032.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___359_1032.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___359_1032.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___359_1032.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___359_1032.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___359_1032.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___359_1032.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___359_1032.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1059 = catch t  in
    bind uu____1059
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1086 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___361_1117  ->
              match () with
              | () -> let uu____1122 = trytac t  in run uu____1122 ps) ()
         with
         | FStar_Errors.Err (uu____1138,msg) ->
             (log ps
                (fun uu____1142  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1147,msg,uu____1149) ->
             (log ps
                (fun uu____1152  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1185 = run t ps  in
           match uu____1185 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1204  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___362_1218 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_1218.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_1218.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___362_1218.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___362_1218.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_1218.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_1218.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_1218.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_1218.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_1218.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_1218.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_1218.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___362_1218.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1239 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1239
         then
           let uu____1240 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1241 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1240
             uu____1241
         else ());
        (try
           (fun uu___364_1248  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1255 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1255
                    then
                      let uu____1256 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1257 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1258 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1256
                        uu____1257 uu____1258
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1263 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1263 (fun uu____1267  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1274,msg) ->
             mlog
               (fun uu____1277  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1279  -> ret false)
         | FStar_Errors.Error (uu____1280,msg,r) ->
             mlog
               (fun uu____1285  ->
                  let uu____1286 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1286) (fun uu____1288  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___365_1299 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___365_1299.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___365_1299.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___365_1299.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___366_1302 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___366_1302.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___366_1302.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___366_1302.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___366_1302.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___366_1302.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___366_1302.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___366_1302.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___366_1302.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___366_1302.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___366_1302.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___366_1302.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___366_1302.FStar_Tactics_Types.local_state)
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
          (fun uu____1325  ->
             (let uu____1327 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1327
              then
                (FStar_Options.push ();
                 (let uu____1329 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1331 = __do_unify env t1 t2  in
              bind uu____1331
                (fun r  ->
                   (let uu____1338 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1338 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1341  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___367_1348 = ps  in
         let uu____1349 =
           FStar_List.filter
             (fun g  ->
                let uu____1355 = check_goal_solved g  in
                FStar_Option.isNone uu____1355) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___367_1348.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___367_1348.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___367_1348.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1349;
           FStar_Tactics_Types.smt_goals =
             (uu___367_1348.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___367_1348.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___367_1348.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___367_1348.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___367_1348.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___367_1348.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___367_1348.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___367_1348.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___367_1348.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1372 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1372 with
      | FStar_Pervasives_Native.Some uu____1377 ->
          let uu____1378 =
            let uu____1379 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1379  in
          fail uu____1378
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1395 = FStar_Tactics_Types.goal_env goal  in
      let uu____1396 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1395 solution uu____1396
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1402 =
         let uu___368_1403 = p  in
         let uu____1404 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___368_1403.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___368_1403.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___368_1403.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1404;
           FStar_Tactics_Types.smt_goals =
             (uu___368_1403.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___368_1403.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___368_1403.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___368_1403.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___368_1403.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___368_1403.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___368_1403.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___368_1403.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___368_1403.FStar_Tactics_Types.local_state)
         }  in
       set uu____1402)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1425  ->
           let uu____1426 =
             let uu____1427 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1427  in
           let uu____1428 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1426 uu____1428)
        (fun uu____1431  ->
           let uu____1432 = trysolve goal solution  in
           bind uu____1432
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1440  -> remove_solved_goals)
                else
                  (let uu____1442 =
                     let uu____1443 =
                       let uu____1444 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1444 solution  in
                     let uu____1445 =
                       let uu____1446 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1447 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1446 uu____1447  in
                     let uu____1448 =
                       let uu____1449 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1450 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1449 uu____1450  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1443 uu____1445 uu____1448
                      in
                   fail uu____1442)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1465 = set_solution goal solution  in
      bind uu____1465
        (fun uu____1469  ->
           bind __dismiss (fun uu____1471  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___369_1489 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1489.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1489.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1489.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___369_1489.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1489.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1489.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1489.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1489.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1489.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1489.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1489.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___369_1489.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___370_1507 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1507.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1507.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1507.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_1507.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___370_1507.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1507.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1507.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1507.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1507.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1507.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1507.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1507.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1528 = FStar_Options.defensive ()  in
    if uu____1528
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1533 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1533)
         in
      let b2 =
        b1 &&
          (let uu____1536 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1536)
         in
      let rec aux b3 e =
        let uu____1548 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1548 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1566 =
        (let uu____1569 = aux b2 env  in Prims.op_Negation uu____1569) &&
          (let uu____1571 = FStar_ST.op_Bang nwarn  in
           uu____1571 < (Prims.parse_int "5"))
         in
      (if uu____1566
       then
         ((let uu____1592 =
             let uu____1593 = FStar_Tactics_Types.goal_type g  in
             uu____1593.FStar_Syntax_Syntax.pos  in
           let uu____1596 =
             let uu____1601 =
               let uu____1602 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1602
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1601)  in
           FStar_Errors.log_issue uu____1592 uu____1596);
          (let uu____1603 =
             let uu____1604 = FStar_ST.op_Bang nwarn  in
             uu____1604 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1603))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___371_1664 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1664.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1664.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1664.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___371_1664.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___371_1664.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1664.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1664.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1664.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1664.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1664.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1664.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1664.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___372_1684 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1684.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1684.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_1684.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___372_1684.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_1684.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1684.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1684.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1684.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_1684.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_1684.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_1684.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_1684.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___373_1704 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___373_1704.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___373_1704.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___373_1704.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___373_1704.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___373_1704.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___373_1704.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___373_1704.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___373_1704.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___373_1704.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___373_1704.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___373_1704.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___373_1704.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___374_1724 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_1724.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_1724.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___374_1724.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___374_1724.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___374_1724.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_1724.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_1724.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_1724.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___374_1724.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___374_1724.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_1724.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_1724.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1735  -> add_goals [g]) 
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
        let uu____1763 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1763 with
        | (u,ctx_uvar,g_u) ->
            let uu____1797 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1797
              (fun uu____1806  ->
                 let uu____1807 =
                   let uu____1812 =
                     let uu____1813 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1813  in
                   (u, uu____1812)  in
                 ret uu____1807)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1831 = FStar_Syntax_Util.un_squash t  in
    match uu____1831 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1841 =
          let uu____1842 = FStar_Syntax_Subst.compress t'  in
          uu____1842.FStar_Syntax_Syntax.n  in
        (match uu____1841 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1846 -> false)
    | uu____1847 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1857 = FStar_Syntax_Util.un_squash t  in
    match uu____1857 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1867 =
          let uu____1868 = FStar_Syntax_Subst.compress t'  in
          uu____1868.FStar_Syntax_Syntax.n  in
        (match uu____1867 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1872 -> false)
    | uu____1873 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1884  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1895 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1895 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1902 = goal_to_string_verbose hd1  in
                    let uu____1903 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1902 uu____1903);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____1913 =
      bind get
        (fun ps  ->
           let uu____1919 = cur_goal ()  in
           bind uu____1919
             (fun g  ->
                (let uu____1926 =
                   let uu____1927 = FStar_Tactics_Types.goal_type g  in
                   uu____1927.FStar_Syntax_Syntax.pos  in
                 let uu____1930 =
                   let uu____1935 =
                     let uu____1936 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1936
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1935)  in
                 FStar_Errors.log_issue uu____1926 uu____1930);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____1913
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1947  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___375_1957 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___375_1957.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___375_1957.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___375_1957.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___375_1957.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___375_1957.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___375_1957.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___375_1957.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___375_1957.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___375_1957.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___375_1957.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___375_1957.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___375_1957.FStar_Tactics_Types.local_state)
           }  in
         let uu____1958 = set ps1  in
         bind uu____1958
           (fun uu____1963  ->
              let uu____1964 = FStar_BigInt.of_int_fs n1  in ret uu____1964))
  
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
            let uu____1992 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1992 phi  in
          let uu____1993 = new_uvar reason env typ  in
          bind uu____1993
            (fun uu____2008  ->
               match uu____2008 with
               | (uu____2015,ctx_uvar) ->
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
             (fun uu____2060  ->
                let uu____2061 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2061)
             (fun uu____2064  ->
                let e1 =
                  let uu___376_2066 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___376_2066.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___376_2066.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___376_2066.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___376_2066.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___376_2066.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___376_2066.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___376_2066.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___376_2066.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___376_2066.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___376_2066.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___376_2066.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___376_2066.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___376_2066.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___376_2066.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___376_2066.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___376_2066.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___376_2066.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___376_2066.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___376_2066.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___376_2066.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___376_2066.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___376_2066.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___376_2066.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___376_2066.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___376_2066.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___376_2066.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___376_2066.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___376_2066.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___376_2066.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___376_2066.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___376_2066.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___376_2066.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___376_2066.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___376_2066.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___376_2066.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___376_2066.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___376_2066.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___376_2066.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___376_2066.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___376_2066.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___378_2077  ->
                     match () with
                     | () ->
                         let uu____2086 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2086) ()
                with
                | FStar_Errors.Err (uu____2113,msg) ->
                    let uu____2115 = tts e1 t  in
                    let uu____2116 =
                      let uu____2117 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2117
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2115 uu____2116 msg
                | FStar_Errors.Error (uu____2124,msg,uu____2126) ->
                    let uu____2127 = tts e1 t  in
                    let uu____2128 =
                      let uu____2129 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2129
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2127 uu____2128 msg))
  
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
             (fun uu____2178  ->
                let uu____2179 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2179)
             (fun uu____2182  ->
                let e1 =
                  let uu___379_2184 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___379_2184.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___379_2184.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___379_2184.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___379_2184.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___379_2184.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___379_2184.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___379_2184.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___379_2184.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___379_2184.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___379_2184.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___379_2184.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___379_2184.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___379_2184.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___379_2184.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___379_2184.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___379_2184.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___379_2184.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___379_2184.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___379_2184.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___379_2184.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___379_2184.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___379_2184.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___379_2184.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___379_2184.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___379_2184.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___379_2184.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___379_2184.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___379_2184.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___379_2184.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___379_2184.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___379_2184.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___379_2184.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___379_2184.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___379_2184.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___379_2184.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___379_2184.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___379_2184.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___379_2184.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___379_2184.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___379_2184.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___381_2198  ->
                     match () with
                     | () ->
                         let uu____2207 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2207 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2245,msg) ->
                    let uu____2247 = tts e1 t  in
                    let uu____2248 =
                      let uu____2249 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2249
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2247 uu____2248 msg
                | FStar_Errors.Error (uu____2256,msg,uu____2258) ->
                    let uu____2259 = tts e1 t  in
                    let uu____2260 =
                      let uu____2261 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2261
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2259 uu____2260 msg))
  
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
             (fun uu____2310  ->
                let uu____2311 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2311)
             (fun uu____2315  ->
                let e1 =
                  let uu___382_2317 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___382_2317.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___382_2317.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___382_2317.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___382_2317.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___382_2317.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___382_2317.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___382_2317.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___382_2317.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___382_2317.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___382_2317.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___382_2317.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___382_2317.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___382_2317.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___382_2317.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___382_2317.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___382_2317.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___382_2317.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___382_2317.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___382_2317.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___382_2317.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___382_2317.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___382_2317.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___382_2317.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___382_2317.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___382_2317.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___382_2317.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___382_2317.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___382_2317.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___382_2317.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___382_2317.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___382_2317.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___382_2317.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___382_2317.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___382_2317.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___382_2317.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___382_2317.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___382_2317.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___382_2317.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___382_2317.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___382_2317.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___383_2319 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___383_2319.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___383_2319.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___383_2319.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___383_2319.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___383_2319.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___383_2319.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___383_2319.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___383_2319.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___383_2319.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___383_2319.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___383_2319.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___383_2319.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___383_2319.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___383_2319.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___383_2319.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___383_2319.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___383_2319.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___383_2319.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___383_2319.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___383_2319.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___383_2319.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___383_2319.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___383_2319.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___383_2319.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___383_2319.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___383_2319.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___383_2319.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___383_2319.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___383_2319.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___383_2319.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___383_2319.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___383_2319.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___383_2319.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___383_2319.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___383_2319.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___383_2319.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___383_2319.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___383_2319.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___383_2319.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___383_2319.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___385_2333  ->
                     match () with
                     | () ->
                         let uu____2342 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2342 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2380,msg) ->
                    let uu____2382 = tts e2 t  in
                    let uu____2383 =
                      let uu____2384 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2384
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2382 uu____2383 msg
                | FStar_Errors.Error (uu____2391,msg,uu____2393) ->
                    let uu____2394 = tts e2 t  in
                    let uu____2395 =
                      let uu____2396 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2396
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2394 uu____2395 msg))
  
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
  fun uu____2423  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___386_2441 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___386_2441.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___386_2441.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___386_2441.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___386_2441.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___386_2441.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___386_2441.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___386_2441.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___386_2441.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___386_2441.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___386_2441.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___386_2441.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___386_2441.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2465 = get_guard_policy ()  in
      bind uu____2465
        (fun old_pol  ->
           let uu____2471 = set_guard_policy pol  in
           bind uu____2471
             (fun uu____2475  ->
                bind t
                  (fun r  ->
                     let uu____2479 = set_guard_policy old_pol  in
                     bind uu____2479 (fun uu____2483  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2486 = let uu____2491 = cur_goal ()  in trytac uu____2491  in
  bind uu____2486
    (fun uu___349_2498  ->
       match uu___349_2498 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2504 = FStar_Options.peek ()  in ret uu____2504)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2526  ->
             let uu____2527 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2527)
          (fun uu____2530  ->
             let uu____2531 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2531
               (fun uu____2535  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2539 =
                         let uu____2540 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2540.FStar_TypeChecker_Env.guard_f  in
                       match uu____2539 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2544 = istrivial e f  in
                           if uu____2544
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2554 =
                                          let uu____2559 =
                                            let uu____2560 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2560
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2559)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2554);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2563  ->
                                           let uu____2564 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2564)
                                        (fun uu____2567  ->
                                           let uu____2568 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2568
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___387_2575 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___387_2575.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___387_2575.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___387_2575.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2578  ->
                                           let uu____2579 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2579)
                                        (fun uu____2582  ->
                                           let uu____2583 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2583
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___388_2590 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___388_2590.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___388_2590.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___388_2590.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2593  ->
                                           let uu____2594 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2594)
                                        (fun uu____2596  ->
                                           try
                                             (fun uu___390_2601  ->
                                                match () with
                                                | () ->
                                                    let uu____2604 =
                                                      let uu____2605 =
                                                        let uu____2606 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2606
                                                         in
                                                      Prims.op_Negation
                                                        uu____2605
                                                       in
                                                    if uu____2604
                                                    then
                                                      mlog
                                                        (fun uu____2611  ->
                                                           let uu____2612 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2612)
                                                        (fun uu____2614  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___389_2617 ->
                                               mlog
                                                 (fun uu____2622  ->
                                                    let uu____2623 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2623)
                                                 (fun uu____2625  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2635 =
      let uu____2638 = cur_goal ()  in
      bind uu____2638
        (fun goal  ->
           let uu____2644 =
             let uu____2653 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____2653 t  in
           bind uu____2644
             (fun uu____2664  ->
                match uu____2664 with
                | (uu____2673,typ,uu____2675) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2635
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2704 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2704 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2715  ->
    let uu____2718 = cur_goal ()  in
    bind uu____2718
      (fun goal  ->
         let uu____2724 =
           let uu____2725 = FStar_Tactics_Types.goal_env goal  in
           let uu____2726 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2725 uu____2726  in
         if uu____2724
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2730 =
              let uu____2731 = FStar_Tactics_Types.goal_env goal  in
              let uu____2732 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2731 uu____2732  in
            fail1 "Not a trivial goal: %s" uu____2730))
  
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
          let uu____2761 =
            let uu____2762 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2762.FStar_TypeChecker_Env.guard_f  in
          match uu____2761 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2770 = istrivial e f  in
              if uu____2770
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2778 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2778
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___391_2788 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___391_2788.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___391_2788.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___391_2788.FStar_Tactics_Types.opts);
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
             let uu____2837 =
               try
                 (fun uu___396_2860  ->
                    match () with
                    | () ->
                        let uu____2871 =
                          let uu____2880 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2880
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2871) ()
               with | uu___395_2890 -> fail "divide: not enough goals"  in
             bind uu____2837
               (fun uu____2926  ->
                  match uu____2926 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___392_2952 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___392_2952.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___392_2952.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___392_2952.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___392_2952.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___392_2952.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___392_2952.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___392_2952.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___392_2952.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___392_2952.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___392_2952.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___392_2952.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2953 = set lp  in
                      bind uu____2953
                        (fun uu____2961  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___393_2977 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___393_2977.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___393_2977.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___393_2977.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___393_2977.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___393_2977.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___393_2977.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___393_2977.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___393_2977.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___393_2977.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___393_2977.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___393_2977.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2978 = set rp  in
                                     bind uu____2978
                                       (fun uu____2986  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___394_3002 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___394_3002.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___394_3002.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3003 = set p'
                                                       in
                                                    bind uu____3003
                                                      (fun uu____3011  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3017 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3038 = divide FStar_BigInt.one f idtac  in
    bind uu____3038
      (fun uu____3051  -> match uu____3051 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3088::uu____3089 ->
             let uu____3092 =
               let uu____3101 = map tau  in
               divide FStar_BigInt.one tau uu____3101  in
             bind uu____3092
               (fun uu____3119  ->
                  match uu____3119 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3160 =
        bind t1
          (fun uu____3165  ->
             let uu____3166 = map t2  in
             bind uu____3166 (fun uu____3174  -> ret ()))
         in
      focus uu____3160
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3183  ->
    let uu____3186 =
      let uu____3189 = cur_goal ()  in
      bind uu____3189
        (fun goal  ->
           let uu____3198 =
             let uu____3205 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3205  in
           match uu____3198 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3214 =
                 let uu____3215 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3215  in
               if uu____3214
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3220 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3220 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3234 = new_uvar "intro" env' typ'  in
                  bind uu____3234
                    (fun uu____3250  ->
                       match uu____3250 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3274 = set_solution goal sol  in
                           bind uu____3274
                             (fun uu____3280  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3282 =
                                  let uu____3285 = bnorm_goal g  in
                                  replace_cur uu____3285  in
                                bind uu____3282 (fun uu____3287  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3292 =
                 let uu____3293 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3294 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3293 uu____3294  in
               fail1 "goal is not an arrow (%s)" uu____3292)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3186
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3309  ->
    let uu____3316 = cur_goal ()  in
    bind uu____3316
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3333 =
            let uu____3340 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3340  in
          match uu____3333 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3353 =
                let uu____3354 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3354  in
              if uu____3353
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3367 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3367
                    in
                 let bs =
                   let uu____3377 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3377; b]  in
                 let env' =
                   let uu____3403 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3403 bs  in
                 let uu____3404 =
                   let uu____3411 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3411  in
                 bind uu____3404
                   (fun uu____3430  ->
                      match uu____3430 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3444 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3447 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3444
                              FStar_Parser_Const.effect_Tot_lid uu____3447 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3465 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3465 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3487 =
                                   let uu____3488 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3488.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3487
                                  in
                               let uu____3501 = set_solution goal tm  in
                               bind uu____3501
                                 (fun uu____3510  ->
                                    let uu____3511 =
                                      let uu____3514 =
                                        bnorm_goal
                                          (let uu___397_3517 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___397_3517.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___397_3517.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___397_3517.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3514  in
                                    bind uu____3511
                                      (fun uu____3524  ->
                                         let uu____3525 =
                                           let uu____3530 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3530, b)  in
                                         ret uu____3525)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3539 =
                let uu____3540 = FStar_Tactics_Types.goal_env goal  in
                let uu____3541 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3540 uu____3541  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3539))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3559 = cur_goal ()  in
    bind uu____3559
      (fun goal  ->
         mlog
           (fun uu____3566  ->
              let uu____3567 =
                let uu____3568 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3568  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3567)
           (fun uu____3573  ->
              let steps =
                let uu____3577 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3577
                 in
              let t =
                let uu____3581 = FStar_Tactics_Types.goal_env goal  in
                let uu____3582 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3581 uu____3582  in
              let uu____3583 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3583))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3607 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____3615 -> g.FStar_Tactics_Types.opts
                 | uu____3618 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____3623  ->
                    let uu____3624 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3624)
                 (fun uu____3627  ->
                    let uu____3628 = __tc_lax e t  in
                    bind uu____3628
                      (fun uu____3649  ->
                         match uu____3649 with
                         | (t1,uu____3659,uu____3660) ->
                             let steps =
                               let uu____3664 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3664
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____3670  ->
                                  let uu____3671 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3671)
                               (fun uu____3673  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3607
  
let (refine_intro : unit -> unit tac) =
  fun uu____3684  ->
    let uu____3687 =
      let uu____3690 = cur_goal ()  in
      bind uu____3690
        (fun g  ->
           let uu____3697 =
             let uu____3708 = FStar_Tactics_Types.goal_env g  in
             let uu____3709 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3708 uu____3709
              in
           match uu____3697 with
           | (uu____3712,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3737 =
                 let uu____3742 =
                   let uu____3747 =
                     let uu____3748 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3748]  in
                   FStar_Syntax_Subst.open_term uu____3747 phi  in
                 match uu____3742 with
                 | (bvs,phi1) ->
                     let uu____3773 =
                       let uu____3774 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3774  in
                     (uu____3773, phi1)
                  in
               (match uu____3737 with
                | (bv1,phi1) ->
                    let uu____3793 =
                      let uu____3796 = FStar_Tactics_Types.goal_env g  in
                      let uu____3797 =
                        let uu____3798 =
                          let uu____3801 =
                            let uu____3802 =
                              let uu____3809 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3809)  in
                            FStar_Syntax_Syntax.NT uu____3802  in
                          [uu____3801]  in
                        FStar_Syntax_Subst.subst uu____3798 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3796
                        uu____3797 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3793
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3817  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3687
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3836 = cur_goal ()  in
      bind uu____3836
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3844 = FStar_Tactics_Types.goal_env goal  in
               let uu____3845 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3844 uu____3845
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3847 = __tc env t  in
           bind uu____3847
             (fun uu____3866  ->
                match uu____3866 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3881  ->
                         let uu____3882 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3883 =
                           let uu____3884 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3884
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3882 uu____3883)
                      (fun uu____3887  ->
                         let uu____3888 =
                           let uu____3891 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3891 guard  in
                         bind uu____3888
                           (fun uu____3893  ->
                              mlog
                                (fun uu____3897  ->
                                   let uu____3898 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3899 =
                                     let uu____3900 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3900
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3898 uu____3899)
                                (fun uu____3903  ->
                                   let uu____3904 =
                                     let uu____3907 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3908 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3907 typ uu____3908  in
                                   bind uu____3904
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3914 =
                                             let uu____3915 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3915 t1  in
                                           let uu____3916 =
                                             let uu____3917 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3917 typ  in
                                           let uu____3918 =
                                             let uu____3919 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3920 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3919 uu____3920  in
                                           let uu____3921 =
                                             let uu____3922 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3923 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3922 uu____3923  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3914 uu____3916 uu____3918
                                             uu____3921)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3943 =
          mlog
            (fun uu____3948  ->
               let uu____3949 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3949)
            (fun uu____3952  ->
               let uu____3953 =
                 let uu____3960 = __exact_now set_expected_typ1 tm  in
                 catch uu____3960  in
               bind uu____3953
                 (fun uu___351_3969  ->
                    match uu___351_3969 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____3980  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____3983  ->
                             let uu____3984 =
                               let uu____3991 =
                                 let uu____3994 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____3994
                                   (fun uu____3999  ->
                                      let uu____4000 = refine_intro ()  in
                                      bind uu____4000
                                        (fun uu____4004  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____3991  in
                             bind uu____3984
                               (fun uu___350_4011  ->
                                  match uu___350_4011 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4020  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4022  -> ret ())
                                  | FStar_Util.Inl uu____4023 ->
                                      mlog
                                        (fun uu____4025  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4027  -> fail e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3943
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4077 = f x  in
          bind uu____4077
            (fun y  ->
               let uu____4085 = mapM f xs  in
               bind uu____4085 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4156 = do_unify e ty1 ty2  in
          bind uu____4156
            (fun uu___352_4168  ->
               if uu___352_4168
               then ret acc
               else
                 (let uu____4187 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4187 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4208 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4209 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4208
                        uu____4209
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4224 =
                        let uu____4225 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4225  in
                      if uu____4224
                      then fail "Codomain is effectful"
                      else
                        (let uu____4245 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4245
                           (fun uu____4271  ->
                              match uu____4271 with
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
      let uu____4357 =
        mlog
          (fun uu____4362  ->
             let uu____4363 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4363)
          (fun uu____4366  ->
             let uu____4367 = cur_goal ()  in
             bind uu____4367
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4375 = __tc e tm  in
                  bind uu____4375
                    (fun uu____4396  ->
                       match uu____4396 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4409 =
                             let uu____4420 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4420  in
                           bind uu____4409
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4463  ->
                                       fun w  ->
                                         match uu____4463 with
                                         | (uvt,q,uu____4481) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4513 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4530  ->
                                       fun s  ->
                                         match uu____4530 with
                                         | (uu____4542,uu____4543,uv) ->
                                             let uu____4545 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4545) uvs uu____4513
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4554 = solve' goal w  in
                                bind uu____4554
                                  (fun uu____4559  ->
                                     let uu____4560 =
                                       mapM
                                         (fun uu____4577  ->
                                            match uu____4577 with
                                            | (uvt,q,uv) ->
                                                let uu____4589 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4589 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4594 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4595 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4595
                                                     then ret ()
                                                     else
                                                       (let uu____4599 =
                                                          let uu____4602 =
                                                            bnorm_goal
                                                              (let uu___398_4605
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___398_4605.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___398_4605.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4602]  in
                                                        add_goals uu____4599)))
                                         uvs
                                        in
                                     bind uu____4560
                                       (fun uu____4609  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4357
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4634 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4634
    then
      let uu____4641 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4656 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4709 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4641 with
      | (pre,post) ->
          let post1 =
            let uu____4741 =
              let uu____4752 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4752]  in
            FStar_Syntax_Util.mk_app post uu____4741  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4782 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4782
       then
         let uu____4789 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4789
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4822 =
      let uu____4825 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4832  ->
                  let uu____4833 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4833)
               (fun uu____4837  ->
                  let is_unit_t t =
                    let uu____4844 =
                      let uu____4845 = FStar_Syntax_Subst.compress t  in
                      uu____4845.FStar_Syntax_Syntax.n  in
                    match uu____4844 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4849 -> false  in
                  let uu____4850 = cur_goal ()  in
                  bind uu____4850
                    (fun goal  ->
                       let uu____4856 =
                         let uu____4865 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4865 tm  in
                       bind uu____4856
                         (fun uu____4880  ->
                            match uu____4880 with
                            | (tm1,t,guard) ->
                                let uu____4892 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4892 with
                                 | (bs,comp) ->
                                     let uu____4925 = lemma_or_sq comp  in
                                     (match uu____4925 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4944 =
                                            FStar_List.fold_left
                                              (fun uu____4992  ->
                                                 fun uu____4993  ->
                                                   match (uu____4992,
                                                           uu____4993)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5106 =
                                                         is_unit_t b_t  in
                                                       if uu____5106
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5144 =
                                                            let uu____5157 =
                                                              let uu____5158
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5158.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5161 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5157
                                                              uu____5161 b_t
                                                             in
                                                          match uu____5144
                                                          with
                                                          | (u,uu____5179,g_u)
                                                              ->
                                                              let uu____5193
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5193,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4944 with
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
                                               let uu____5272 =
                                                 let uu____5275 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5276 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5277 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5275
                                                   uu____5276 uu____5277
                                                  in
                                               bind uu____5272
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5285 =
                                                        let uu____5286 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5286 tm1
                                                         in
                                                      let uu____5287 =
                                                        let uu____5288 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5289 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5288
                                                          uu____5289
                                                         in
                                                      let uu____5290 =
                                                        let uu____5291 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5292 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5291
                                                          uu____5292
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5285 uu____5287
                                                        uu____5290
                                                    else
                                                      (let uu____5294 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5294
                                                         (fun uu____5299  ->
                                                            let uu____5300 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5300
                                                              (fun uu____5308
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5333
                                                                    =
                                                                    let uu____5336
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5336
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5333
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
                                                                    let uu____5371
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5371)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5387
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5387
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5405)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5431)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5448
                                                                    -> false)
                                                                    in
                                                                 let uu____5449
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
                                                                    let uu____5479
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5479
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5501)
                                                                    ->
                                                                    let uu____5526
                                                                    =
                                                                    let uu____5527
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5527.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5526
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5535)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___399_5555
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___399_5555.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___399_5555.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___399_5555.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5558
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5564
                                                                     ->
                                                                    let uu____5565
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5566
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5565
                                                                    uu____5566)
                                                                    (fun
                                                                    uu____5571
                                                                     ->
                                                                    let env =
                                                                    let uu___400_5573
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___400_5573.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5575
                                                                    =
                                                                    let uu____5578
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5579
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5580
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5579
                                                                    uu____5580
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5582
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5578
                                                                    uu____5582
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5575
                                                                    (fun
                                                                    uu____5586
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5449
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
                                                                    let uu____5648
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5648
                                                                    then
                                                                    let uu____5651
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5651
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
                                                                    let uu____5665
                                                                    =
                                                                    let uu____5666
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5666
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5665)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5667
                                                                    =
                                                                    let uu____5670
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5670
                                                                    guard  in
                                                                    bind
                                                                    uu____5667
                                                                    (fun
                                                                    uu____5673
                                                                     ->
                                                                    let uu____5674
                                                                    =
                                                                    let uu____5677
                                                                    =
                                                                    let uu____5678
                                                                    =
                                                                    let uu____5679
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5680
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5679
                                                                    uu____5680
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5678
                                                                     in
                                                                    if
                                                                    uu____5677
                                                                    then
                                                                    let uu____5683
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5683
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5674
                                                                    (fun
                                                                    uu____5686
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4825  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4822
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5708 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5708 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5718::(e1,uu____5720)::(e2,uu____5722)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5783 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5807 = destruct_eq' typ  in
    match uu____5807 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5837 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5837 with
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
        let uu____5899 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5899 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5947 = aux e'  in
               FStar_Util.map_opt uu____5947
                 (fun uu____5971  ->
                    match uu____5971 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5992 = aux e  in
      FStar_Util.map_opt uu____5992
        (fun uu____6016  ->
           match uu____6016 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____6083 =
            let uu____6092 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6092  in
          FStar_Util.map_opt uu____6083
            (fun uu____6107  ->
               match uu____6107 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___401_6126 = bv  in
                     let uu____6127 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___401_6126.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___401_6126.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6127
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___402_6135 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6136 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6145 =
                       let uu____6148 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6148  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___402_6135.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6136;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6145;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___402_6135.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___402_6135.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___402_6135.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___403_6149 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___403_6149.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___403_6149.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___403_6149.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6159 =
      let uu____6162 = cur_goal ()  in
      bind uu____6162
        (fun goal  ->
           let uu____6170 = h  in
           match uu____6170 with
           | (bv,uu____6174) ->
               mlog
                 (fun uu____6182  ->
                    let uu____6183 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6184 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6183
                      uu____6184)
                 (fun uu____6187  ->
                    let uu____6188 =
                      let uu____6197 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6197  in
                    match uu____6188 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6218 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6218 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6233 =
                               let uu____6234 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6234.FStar_Syntax_Syntax.n  in
                             (match uu____6233 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___404_6251 = bv1  in
                                    let uu____6252 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___404_6251.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___404_6251.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6252
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___405_6260 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6261 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6270 =
                                      let uu____6273 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6273
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___405_6260.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6261;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6270;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___405_6260.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___405_6260.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___405_6260.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___406_6276 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___406_6276.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___406_6276.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___406_6276.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6277 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6278 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6159
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6303 =
        let uu____6306 = cur_goal ()  in
        bind uu____6306
          (fun goal  ->
             let uu____6317 = b  in
             match uu____6317 with
             | (bv,uu____6321) ->
                 let bv' =
                   let uu____6327 =
                     let uu___407_6328 = bv  in
                     let uu____6329 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6329;
                       FStar_Syntax_Syntax.index =
                         (uu___407_6328.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___407_6328.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6327  in
                 let s1 =
                   let uu____6333 =
                     let uu____6334 =
                       let uu____6341 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6341)  in
                     FStar_Syntax_Syntax.NT uu____6334  in
                   [uu____6333]  in
                 let uu____6346 = subst_goal bv bv' s1 goal  in
                 (match uu____6346 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6303
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6365 =
      let uu____6368 = cur_goal ()  in
      bind uu____6368
        (fun goal  ->
           let uu____6377 = b  in
           match uu____6377 with
           | (bv,uu____6381) ->
               let uu____6386 =
                 let uu____6395 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6395  in
               (match uu____6386 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6416 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6416 with
                     | (ty,u) ->
                         let uu____6425 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6425
                           (fun uu____6443  ->
                              match uu____6443 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___408_6453 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___408_6453.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___408_6453.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6457 =
                                      let uu____6458 =
                                        let uu____6465 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6465)  in
                                      FStar_Syntax_Syntax.NT uu____6458  in
                                    [uu____6457]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___409_6477 = b1  in
                                         let uu____6478 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___409_6477.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___409_6477.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6478
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6485  ->
                                       let new_goal =
                                         let uu____6487 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6488 =
                                           let uu____6489 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6489
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6487 uu____6488
                                          in
                                       let uu____6490 = add_goals [new_goal]
                                          in
                                       bind uu____6490
                                         (fun uu____6495  ->
                                            let uu____6496 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6496
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6365
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6519 =
        let uu____6522 = cur_goal ()  in
        bind uu____6522
          (fun goal  ->
             let uu____6531 = b  in
             match uu____6531 with
             | (bv,uu____6535) ->
                 let uu____6540 =
                   let uu____6549 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6549  in
                 (match uu____6540 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6573 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6573
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___410_6578 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___410_6578.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___410_6578.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6580 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6580))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6519
  
let (revert : unit -> unit tac) =
  fun uu____6591  ->
    let uu____6594 = cur_goal ()  in
    bind uu____6594
      (fun goal  ->
         let uu____6600 =
           let uu____6607 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6607  in
         match uu____6600 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6623 =
                 let uu____6626 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6626  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6623
                in
             let uu____6641 = new_uvar "revert" env' typ'  in
             bind uu____6641
               (fun uu____6656  ->
                  match uu____6656 with
                  | (r,u_r) ->
                      let uu____6665 =
                        let uu____6668 =
                          let uu____6669 =
                            let uu____6670 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6670.FStar_Syntax_Syntax.pos  in
                          let uu____6673 =
                            let uu____6678 =
                              let uu____6679 =
                                let uu____6688 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6688  in
                              [uu____6679]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6678  in
                          uu____6673 FStar_Pervasives_Native.None uu____6669
                           in
                        set_solution goal uu____6668  in
                      bind uu____6665
                        (fun uu____6709  ->
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
      let uu____6721 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6721
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6736 = cur_goal ()  in
    bind uu____6736
      (fun goal  ->
         mlog
           (fun uu____6744  ->
              let uu____6745 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6746 =
                let uu____6747 =
                  let uu____6748 =
                    let uu____6757 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6757  in
                  FStar_All.pipe_right uu____6748 FStar_List.length  in
                FStar_All.pipe_right uu____6747 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6745 uu____6746)
           (fun uu____6774  ->
              let uu____6775 =
                let uu____6784 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6784  in
              match uu____6775 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6823 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6823
                        then
                          let uu____6826 =
                            let uu____6827 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6827
                             in
                          fail uu____6826
                        else check1 bvs2
                     in
                  let uu____6829 =
                    let uu____6830 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6830  in
                  if uu____6829
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6834 = check1 bvs  in
                     bind uu____6834
                       (fun uu____6840  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6842 =
                            let uu____6849 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6849  in
                          bind uu____6842
                            (fun uu____6858  ->
                               match uu____6858 with
                               | (ut,uvar_ut) ->
                                   let uu____6867 = set_solution goal ut  in
                                   bind uu____6867
                                     (fun uu____6872  ->
                                        let uu____6873 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6873))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6880  ->
    let uu____6883 = cur_goal ()  in
    bind uu____6883
      (fun goal  ->
         let uu____6889 =
           let uu____6896 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6896  in
         match uu____6889 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6904) ->
             let uu____6909 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6909)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6919 = cur_goal ()  in
    bind uu____6919
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6929 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6929  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6932  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6942 = cur_goal ()  in
    bind uu____6942
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6952 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6952  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6955  -> add_goals [g']))
  
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
            let uu____6995 = FStar_Syntax_Subst.compress t  in
            uu____6995.FStar_Syntax_Syntax.n  in
          let uu____6998 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___414_7004 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___414_7004.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___414_7004.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6998
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7020 =
                   let uu____7021 = FStar_Syntax_Subst.compress t1  in
                   uu____7021.FStar_Syntax_Syntax.n  in
                 match uu____7020 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____7052 = ff hd1  in
                     bind uu____7052
                       (fun hd2  ->
                          let fa uu____7078 =
                            match uu____7078 with
                            | (a,q) ->
                                let uu____7099 = ff a  in
                                bind uu____7099 (fun a1  -> ret (a1, q))
                             in
                          let uu____7118 = mapM fa args  in
                          bind uu____7118
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7200 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7200 with
                      | (bs1,t') ->
                          let uu____7209 =
                            let uu____7212 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7212 t'  in
                          bind uu____7209
                            (fun t''  ->
                               let uu____7216 =
                                 let uu____7217 =
                                   let uu____7236 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7245 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7236, uu____7245, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7217  in
                               ret uu____7216))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7320 = ff hd1  in
                     bind uu____7320
                       (fun hd2  ->
                          let ffb br =
                            let uu____7335 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7335 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7367 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7367  in
                                let uu____7368 = ff1 e  in
                                bind uu____7368
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7383 = mapM ffb brs  in
                          bind uu____7383
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7427;
                          FStar_Syntax_Syntax.lbtyp = uu____7428;
                          FStar_Syntax_Syntax.lbeff = uu____7429;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7431;
                          FStar_Syntax_Syntax.lbpos = uu____7432;_}::[]),e)
                     ->
                     let lb =
                       let uu____7457 =
                         let uu____7458 = FStar_Syntax_Subst.compress t1  in
                         uu____7458.FStar_Syntax_Syntax.n  in
                       match uu____7457 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7462) -> lb
                       | uu____7475 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7484 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7484
                         (fun def1  ->
                            ret
                              (let uu___411_7490 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___411_7490.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___411_7490.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___411_7490.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___411_7490.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___411_7490.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___411_7490.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7491 = fflb lb  in
                     bind uu____7491
                       (fun lb1  ->
                          let uu____7501 =
                            let uu____7506 =
                              let uu____7507 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7507]  in
                            FStar_Syntax_Subst.open_term uu____7506 e  in
                          match uu____7501 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7537 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7537  in
                              let uu____7538 = ff1 e1  in
                              bind uu____7538
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7579 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7579
                         (fun def  ->
                            ret
                              (let uu___412_7585 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___412_7585.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___412_7585.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___412_7585.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___412_7585.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___412_7585.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___412_7585.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7586 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7586 with
                      | (lbs1,e1) ->
                          let uu____7601 = mapM fflb lbs1  in
                          bind uu____7601
                            (fun lbs2  ->
                               let uu____7613 = ff e1  in
                               bind uu____7613
                                 (fun e2  ->
                                    let uu____7621 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7621 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7689 = ff t2  in
                     bind uu____7689
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7720 = ff t2  in
                     bind uu____7720
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7727 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___413_7734 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___413_7734.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___413_7734.FStar_Syntax_Syntax.vars)
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
            let uu____7771 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___415_7780 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___415_7780.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___415_7780.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___415_7780.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___415_7780.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___415_7780.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___415_7780.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___415_7780.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___415_7780.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___415_7780.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___415_7780.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___415_7780.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___415_7780.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___415_7780.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___415_7780.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___415_7780.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___415_7780.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___415_7780.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___415_7780.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___415_7780.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___415_7780.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___415_7780.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___415_7780.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___415_7780.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___415_7780.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___415_7780.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___415_7780.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___415_7780.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___415_7780.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___415_7780.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___415_7780.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___415_7780.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___415_7780.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___415_7780.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___415_7780.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___415_7780.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___415_7780.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___415_7780.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___415_7780.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___415_7780.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___415_7780.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7771 with
            | (t1,lcomp,g) ->
                let uu____7786 =
                  (let uu____7789 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7789) ||
                    (let uu____7791 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7791)
                   in
                if uu____7786
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7799 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7799
                       (fun uu____7815  ->
                          match uu____7815 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7828  ->
                                    let uu____7829 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7830 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7829 uu____7830);
                               (let uu____7831 =
                                  let uu____7834 =
                                    let uu____7835 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7835 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7834
                                    opts
                                   in
                                bind uu____7831
                                  (fun uu____7838  ->
                                     let uu____7839 =
                                       bind tau
                                         (fun uu____7845  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7851  ->
                                                 let uu____7852 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7853 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7852 uu____7853);
                                            ret ut1)
                                        in
                                     focus uu____7839))))
                      in
                   let uu____7854 = catch rewrite_eq  in
                   bind uu____7854
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
          let uu____8052 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____8052
            (fun t1  ->
               let uu____8060 =
                 f env
                   (let uu___418_8069 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___418_8069.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___418_8069.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____8060
                 (fun uu____8085  ->
                    match uu____8085 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____8108 =
                               let uu____8109 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____8109.FStar_Syntax_Syntax.n  in
                             match uu____8108 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8146 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8146
                                   (fun uu____8171  ->
                                      match uu____8171 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8187 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8187
                                            (fun uu____8214  ->
                                               match uu____8214 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___416_8244 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___416_8244.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___416_8244.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8286 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8286 with
                                  | (bs1,t') ->
                                      let uu____8301 =
                                        let uu____8308 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8308 ctrl1 t'
                                         in
                                      bind uu____8301
                                        (fun uu____8326  ->
                                           match uu____8326 with
                                           | (t'',ctrl2) ->
                                               let uu____8341 =
                                                 let uu____8348 =
                                                   let uu___417_8351 = t4  in
                                                   let uu____8354 =
                                                     let uu____8355 =
                                                       let uu____8374 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8383 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8374,
                                                         uu____8383, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8355
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8354;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___417_8351.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___417_8351.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8348, ctrl2)  in
                                               ret uu____8341))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8436 -> ret (t3, ctrl1))))

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
              let uu____8483 = ctrl_tac_fold f env ctrl t  in
              bind uu____8483
                (fun uu____8507  ->
                   match uu____8507 with
                   | (t1,ctrl1) ->
                       let uu____8522 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8522
                         (fun uu____8549  ->
                            match uu____8549 with
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
              let uu____8633 =
                let uu____8640 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8640
                  (fun uu____8649  ->
                     let uu____8650 = ctrl t1  in
                     bind uu____8650
                       (fun res  ->
                          let uu____8673 = trivial ()  in
                          bind uu____8673 (fun uu____8681  -> ret res)))
                 in
              bind uu____8633
                (fun uu____8697  ->
                   match uu____8697 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8721 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___419_8730 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___419_8730.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___419_8730.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___419_8730.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___419_8730.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___419_8730.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___419_8730.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___419_8730.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___419_8730.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___419_8730.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___419_8730.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___419_8730.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___419_8730.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___419_8730.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___419_8730.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___419_8730.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___419_8730.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___419_8730.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___419_8730.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___419_8730.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___419_8730.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___419_8730.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___419_8730.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___419_8730.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___419_8730.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___419_8730.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___419_8730.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___419_8730.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___419_8730.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___419_8730.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___419_8730.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___419_8730.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___419_8730.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___419_8730.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___419_8730.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___419_8730.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___419_8730.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___419_8730.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___419_8730.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___419_8730.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___419_8730.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8721 with
                          | (t2,lcomp,g) ->
                              let uu____8740 =
                                (let uu____8743 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8743) ||
                                  (let uu____8745 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8745)
                                 in
                              if uu____8740
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8758 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8758
                                   (fun uu____8778  ->
                                      match uu____8778 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8795  ->
                                                let uu____8796 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8797 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8796 uu____8797);
                                           (let uu____8798 =
                                              let uu____8801 =
                                                let uu____8802 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8802 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8801 opts
                                               in
                                            bind uu____8798
                                              (fun uu____8809  ->
                                                 let uu____8810 =
                                                   bind rewriter
                                                     (fun uu____8824  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8830  ->
                                                             let uu____8831 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8832 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8831
                                                               uu____8832);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8810)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8873 =
        bind get
          (fun ps  ->
             let uu____8883 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8883 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8920  ->
                       let uu____8921 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8921);
                  bind dismiss_all
                    (fun uu____8924  ->
                       let uu____8925 =
                         let uu____8932 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8932
                           keepGoing gt1
                          in
                       bind uu____8925
                         (fun uu____8944  ->
                            match uu____8944 with
                            | (gt',uu____8952) ->
                                (log ps
                                   (fun uu____8956  ->
                                      let uu____8957 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8957);
                                 (let uu____8958 = push_goals gs  in
                                  bind uu____8958
                                    (fun uu____8963  ->
                                       let uu____8964 =
                                         let uu____8967 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8967]  in
                                       add_goals uu____8964)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8873
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8990 =
        bind get
          (fun ps  ->
             let uu____9000 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9000 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9037  ->
                       let uu____9038 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____9038);
                  bind dismiss_all
                    (fun uu____9041  ->
                       let uu____9042 =
                         let uu____9045 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____9045 gt1
                          in
                       bind uu____9042
                         (fun gt'  ->
                            log ps
                              (fun uu____9053  ->
                                 let uu____9054 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____9054);
                            (let uu____9055 = push_goals gs  in
                             bind uu____9055
                               (fun uu____9060  ->
                                  let uu____9061 =
                                    let uu____9064 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____9064]  in
                                  add_goals uu____9061))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8990
  
let (trefl : unit -> unit tac) =
  fun uu____9075  ->
    let uu____9078 =
      let uu____9081 = cur_goal ()  in
      bind uu____9081
        (fun g  ->
           let uu____9099 =
             let uu____9104 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____9104  in
           match uu____9099 with
           | FStar_Pervasives_Native.Some t ->
               let uu____9112 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____9112 with
                | (hd1,args) ->
                    let uu____9151 =
                      let uu____9164 =
                        let uu____9165 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9165.FStar_Syntax_Syntax.n  in
                      (uu____9164, args)  in
                    (match uu____9151 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9179::(l,uu____9181)::(r,uu____9183)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9230 =
                           let uu____9233 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9233 l r  in
                         bind uu____9230
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9240 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9240 l
                                    in
                                 let r1 =
                                   let uu____9242 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9242 r
                                    in
                                 let uu____9243 =
                                   let uu____9246 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9246 l1 r1  in
                                 bind uu____9243
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9252 =
                                           let uu____9253 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9253 l1  in
                                         let uu____9254 =
                                           let uu____9255 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9255 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9252 uu____9254))))
                     | (hd2,uu____9257) ->
                         let uu____9274 =
                           let uu____9275 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9275 t  in
                         fail1 "trefl: not an equality (%s)" uu____9274))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____9078
  
let (dup : unit -> unit tac) =
  fun uu____9288  ->
    let uu____9291 = cur_goal ()  in
    bind uu____9291
      (fun g  ->
         let uu____9297 =
           let uu____9304 = FStar_Tactics_Types.goal_env g  in
           let uu____9305 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9304 uu____9305  in
         bind uu____9297
           (fun uu____9314  ->
              match uu____9314 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___420_9324 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___420_9324.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___420_9324.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___420_9324.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9327  ->
                       let uu____9328 =
                         let uu____9331 = FStar_Tactics_Types.goal_env g  in
                         let uu____9332 =
                           let uu____9333 =
                             let uu____9334 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9335 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9334
                               uu____9335
                              in
                           let uu____9336 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9337 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9333 uu____9336 u
                             uu____9337
                            in
                         add_irrelevant_goal "dup equation" uu____9331
                           uu____9332 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9328
                         (fun uu____9340  ->
                            let uu____9341 = add_goals [g']  in
                            bind uu____9341 (fun uu____9345  -> ret ())))))
  
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
              let uu____9468 = f x y  in
              if uu____9468 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9488 -> (acc, l11, l21)  in
        let uu____9503 = aux [] l1 l2  in
        match uu____9503 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9608 = get_phi g1  in
      match uu____9608 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9614 = get_phi g2  in
          (match uu____9614 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9626 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9626 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9657 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____9657 phi1  in
                    let t2 =
                      let uu____9667 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____9667 phi2  in
                    let uu____9676 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9676
                      (fun uu____9681  ->
                         let uu____9682 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9682
                           (fun uu____9689  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___421_9694 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9695 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___421_9694.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___421_9694.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___421_9694.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___421_9694.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9695;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___421_9694.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___421_9694.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___421_9694.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___421_9694.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___421_9694.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___421_9694.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___421_9694.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___421_9694.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___421_9694.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___421_9694.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___421_9694.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___421_9694.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___421_9694.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___421_9694.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___421_9694.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___421_9694.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___421_9694.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___421_9694.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___421_9694.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___421_9694.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___421_9694.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___421_9694.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___421_9694.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___421_9694.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___421_9694.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___421_9694.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___421_9694.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___421_9694.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___421_9694.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___421_9694.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___421_9694.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___421_9694.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___421_9694.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___421_9694.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___421_9694.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9698 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                 in
                              bind uu____9698
                                (fun goal  ->
                                   mlog
                                     (fun uu____9707  ->
                                        let uu____9708 =
                                          goal_to_string_verbose g1  in
                                        let uu____9709 =
                                          goal_to_string_verbose g2  in
                                        let uu____9710 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9708 uu____9709 uu____9710)
                                     (fun uu____9712  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9719  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9735 =
               set
                 (let uu___422_9740 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___422_9740.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___422_9740.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___422_9740.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___422_9740.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___422_9740.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___422_9740.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___422_9740.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___422_9740.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___422_9740.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___422_9740.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___422_9740.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___422_9740.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9735
               (fun uu____9743  ->
                  let uu____9744 = join_goals g1 g2  in
                  bind uu____9744 (fun g12  -> add_goals [g12]))
         | uu____9749 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9769 =
      let uu____9776 = cur_goal ()  in
      bind uu____9776
        (fun g  ->
           let uu____9786 =
             let uu____9795 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9795 t  in
           bind uu____9786
             (fun uu____9823  ->
                match uu____9823 with
                | (t1,typ,guard) ->
                    let uu____9839 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9839 with
                     | (hd1,args) ->
                         let uu____9888 =
                           let uu____9903 =
                             let uu____9904 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9904.FStar_Syntax_Syntax.n  in
                           (uu____9903, args)  in
                         (match uu____9888 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9925)::(q,uu____9927)::[]) when
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
                                let uu____9981 =
                                  let uu____9982 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9982
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9981
                                 in
                              let g2 =
                                let uu____9984 =
                                  let uu____9985 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9985
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9984
                                 in
                              bind __dismiss
                                (fun uu____9992  ->
                                   let uu____9993 = add_goals [g1; g2]  in
                                   bind uu____9993
                                     (fun uu____10002  ->
                                        let uu____10003 =
                                          let uu____10008 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____10009 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____10008, uu____10009)  in
                                        ret uu____10003))
                          | uu____10014 ->
                              let uu____10029 =
                                let uu____10030 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____10030 typ  in
                              fail1 "Not a disjunction: %s" uu____10029))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9769
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____10060 =
      let uu____10063 = cur_goal ()  in
      bind uu____10063
        (fun g  ->
           FStar_Options.push ();
           (let uu____10076 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____10076);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___423_10083 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___423_10083.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___423_10083.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___423_10083.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____10060
  
let (top_env : unit -> env tac) =
  fun uu____10095  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10108  ->
    let uu____10111 = cur_goal ()  in
    bind uu____10111
      (fun g  ->
         let uu____10117 =
           (FStar_Options.lax ()) ||
             (let uu____10119 = FStar_Tactics_Types.goal_env g  in
              uu____10119.FStar_TypeChecker_Env.lax)
            in
         ret uu____10117)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10134 =
        mlog
          (fun uu____10139  ->
             let uu____10140 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10140)
          (fun uu____10143  ->
             let uu____10144 = cur_goal ()  in
             bind uu____10144
               (fun goal  ->
                  let env =
                    let uu____10152 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10152 ty  in
                  let uu____10153 = __tc_ghost env tm  in
                  bind uu____10153
                    (fun uu____10172  ->
                       match uu____10172 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10186  ->
                                let uu____10187 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10187)
                             (fun uu____10189  ->
                                mlog
                                  (fun uu____10192  ->
                                     let uu____10193 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10193)
                                  (fun uu____10196  ->
                                     let uu____10197 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10197
                                       (fun uu____10201  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10134
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10224 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10230 =
              let uu____10237 =
                let uu____10238 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10238
                 in
              new_uvar "uvar_env.2" env uu____10237  in
            bind uu____10230
              (fun uu____10254  ->
                 match uu____10254 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10224
        (fun typ  ->
           let uu____10266 = new_uvar "uvar_env" env typ  in
           bind uu____10266
             (fun uu____10280  ->
                match uu____10280 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10298 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10317 -> g.FStar_Tactics_Types.opts
             | uu____10320 -> FStar_Options.peek ()  in
           let uu____10323 = FStar_Syntax_Util.head_and_args t  in
           match uu____10323 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10343);
                FStar_Syntax_Syntax.pos = uu____10344;
                FStar_Syntax_Syntax.vars = uu____10345;_},uu____10346)
               ->
               let env1 =
                 let uu___424_10388 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___424_10388.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___424_10388.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___424_10388.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___424_10388.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___424_10388.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___424_10388.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___424_10388.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___424_10388.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___424_10388.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___424_10388.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___424_10388.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___424_10388.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___424_10388.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___424_10388.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___424_10388.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___424_10388.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___424_10388.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___424_10388.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___424_10388.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___424_10388.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___424_10388.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___424_10388.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___424_10388.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___424_10388.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___424_10388.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___424_10388.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___424_10388.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___424_10388.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___424_10388.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___424_10388.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___424_10388.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___424_10388.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___424_10388.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___424_10388.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___424_10388.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___424_10388.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___424_10388.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___424_10388.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___424_10388.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___424_10388.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____10390 =
                 let uu____10393 = bnorm_goal g  in [uu____10393]  in
               add_goals uu____10390
           | uu____10394 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10298
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10443 = if b then t2 else ret false  in
             bind uu____10443 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10454 = trytac comp  in
      bind uu____10454
        (fun uu___353_10462  ->
           match uu___353_10462 with
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
        let uu____10488 =
          bind get
            (fun ps  ->
               let uu____10494 = __tc e t1  in
               bind uu____10494
                 (fun uu____10514  ->
                    match uu____10514 with
                    | (t11,ty1,g1) ->
                        let uu____10526 = __tc e t2  in
                        bind uu____10526
                          (fun uu____10546  ->
                             match uu____10546 with
                             | (t21,ty2,g2) ->
                                 let uu____10558 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10558
                                   (fun uu____10563  ->
                                      let uu____10564 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10564
                                        (fun uu____10570  ->
                                           let uu____10571 =
                                             do_unify e ty1 ty2  in
                                           let uu____10574 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10571 uu____10574)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10488
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10607  ->
             let uu____10608 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10608
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
        (fun uu____10629  ->
           let uu____10630 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10630)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10640 =
      mlog
        (fun uu____10645  ->
           let uu____10646 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10646)
        (fun uu____10649  ->
           let uu____10650 = cur_goal ()  in
           bind uu____10650
             (fun g  ->
                let uu____10656 =
                  let uu____10665 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10665 ty  in
                bind uu____10656
                  (fun uu____10677  ->
                     match uu____10677 with
                     | (ty1,uu____10687,guard) ->
                         let uu____10689 =
                           let uu____10692 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10692 guard  in
                         bind uu____10689
                           (fun uu____10695  ->
                              let uu____10696 =
                                let uu____10699 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10700 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10699 uu____10700 ty1  in
                              bind uu____10696
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10706 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10706
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10712 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10713 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10712
                                          uu____10713
                                         in
                                      let nty =
                                        let uu____10715 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10715 ty1  in
                                      let uu____10716 =
                                        let uu____10719 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10719 ng nty  in
                                      bind uu____10716
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10725 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10725
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10640
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10788 =
      let uu____10797 = cur_goal ()  in
      bind uu____10797
        (fun g  ->
           let uu____10809 =
             let uu____10818 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10818 s_tm  in
           bind uu____10809
             (fun uu____10836  ->
                match uu____10836 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10854 =
                      let uu____10857 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10857 guard  in
                    bind uu____10854
                      (fun uu____10869  ->
                         let uu____10870 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10870 with
                         | (h,args) ->
                             let uu____10915 =
                               let uu____10922 =
                                 let uu____10923 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10923.FStar_Syntax_Syntax.n  in
                               match uu____10922 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10938;
                                      FStar_Syntax_Syntax.vars = uu____10939;_},us)
                                   -> ret (fv, us)
                               | uu____10949 -> fail "type is not an fv"  in
                             bind uu____10915
                               (fun uu____10969  ->
                                  match uu____10969 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10985 =
                                        let uu____10988 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10988 t_lid
                                         in
                                      (match uu____10985 with
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
                                                  (fun uu____11037  ->
                                                     let uu____11038 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____11038 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____11053 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____11081
                                                                  =
                                                                  let uu____11084
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____11084
                                                                    c_lid
                                                                   in
                                                                match uu____11081
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
                                                                    uu____11154
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
                                                                    let uu____11159
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11159
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11182
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11182
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11225
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11225
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11298
                                                                    =
                                                                    let uu____11299
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11299
                                                                     in
                                                                    failwhen
                                                                    uu____11298
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11316
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
                                                                    uu___354_11332
                                                                    =
                                                                    match uu___354_11332
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11335)
                                                                    -> true
                                                                    | 
                                                                    uu____11336
                                                                    -> false
                                                                     in
                                                                    let uu____11339
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11339
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
                                                                    uu____11472
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
                                                                    uu____11534
                                                                     ->
                                                                    match uu____11534
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11554),
                                                                    (t,uu____11556))
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
                                                                    uu____11624
                                                                     ->
                                                                    match uu____11624
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11650),
                                                                    (t,uu____11652))
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
                                                                    uu____11707
                                                                     ->
                                                                    match uu____11707
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
                                                                    let uu____11757
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___425_11774
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___425_11774.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____11757
                                                                    with
                                                                    | 
                                                                    (uu____11787,uu____11788,uu____11789,pat_t,uu____11791,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11798
                                                                    =
                                                                    let uu____11799
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11799
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11798
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11803
                                                                    =
                                                                    let uu____11812
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11812]
                                                                     in
                                                                    let uu____11831
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11803
                                                                    uu____11831
                                                                     in
                                                                    let nty =
                                                                    let uu____11837
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11837
                                                                     in
                                                                    let uu____11840
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11840
                                                                    (fun
                                                                    uu____11869
                                                                     ->
                                                                    match uu____11869
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
                                                                    let uu____11895
                                                                    =
                                                                    let uu____11906
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11906]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11895
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11942
                                                                    =
                                                                    let uu____11953
                                                                    =
                                                                    let uu____11958
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11958)
                                                                     in
                                                                    (g', br,
                                                                    uu____11953)
                                                                     in
                                                                    ret
                                                                    uu____11942))))))
                                                                    | 
                                                                    uu____11979
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____11053
                                                           (fun goal_brs  ->
                                                              let uu____12028
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____12028
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
                                                                  let uu____12101
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12101
                                                                    (
                                                                    fun
                                                                    uu____12112
                                                                     ->
                                                                    let uu____12113
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12113
                                                                    (fun
                                                                    uu____12123
                                                                     ->
                                                                    ret infos))))
                                            | uu____12130 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10788
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12175::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12203 = init xs  in x :: uu____12203
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12215 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12224) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12289 = last args  in
          (match uu____12289 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12319 =
                 let uu____12320 =
                   let uu____12325 =
                     let uu____12326 =
                       let uu____12331 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12331  in
                     uu____12326 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12325, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12320  in
               FStar_All.pipe_left ret uu____12319)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12344,uu____12345) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12397 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12397 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12438 =
                      let uu____12439 =
                        let uu____12444 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12444)  in
                      FStar_Reflection_Data.Tv_Abs uu____12439  in
                    FStar_All.pipe_left ret uu____12438))
      | FStar_Syntax_Syntax.Tm_type uu____12447 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12471 ->
          let uu____12486 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12486 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12516 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12516 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12569 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12581 =
            let uu____12582 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12582  in
          FStar_All.pipe_left ret uu____12581
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12603 =
            let uu____12604 =
              let uu____12609 =
                let uu____12610 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12610  in
              (uu____12609, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12604  in
          FStar_All.pipe_left ret uu____12603
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12644 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12649 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12649 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12702 ->
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
             | FStar_Util.Inr uu____12736 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12740 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12740 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12760 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12764 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12818 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12818
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12837 =
                  let uu____12844 =
                    FStar_List.map
                      (fun uu____12856  ->
                         match uu____12856 with
                         | (p1,uu____12864) -> inspect_pat p1) ps
                     in
                  (fv, uu____12844)  in
                FStar_Reflection_Data.Pat_Cons uu____12837
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
              (fun uu___355_12958  ->
                 match uu___355_12958 with
                 | (pat,uu____12980,t5) ->
                     let uu____12998 = inspect_pat pat  in (uu____12998, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____13007 ->
          ((let uu____13009 =
              let uu____13014 =
                let uu____13015 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____13016 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____13015 uu____13016
                 in
              (FStar_Errors.Warning_CantInspect, uu____13014)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____13009);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12215
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____13029 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____13029
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____13033 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____13033
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____13037 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____13037
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____13044 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____13044
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____13069 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____13069
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____13086 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____13086
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13105 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13105
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13109 =
          let uu____13110 =
            let uu____13117 =
              let uu____13118 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13118  in
            FStar_Syntax_Syntax.mk uu____13117  in
          uu____13110 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13109
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13126 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13126
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13135 =
          let uu____13136 =
            let uu____13143 =
              let uu____13144 =
                let uu____13157 =
                  let uu____13160 =
                    let uu____13161 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13161]  in
                  FStar_Syntax_Subst.close uu____13160 t2  in
                ((false, [lb]), uu____13157)  in
              FStar_Syntax_Syntax.Tm_let uu____13144  in
            FStar_Syntax_Syntax.mk uu____13143  in
          uu____13136 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13135
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13201 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13201 with
         | (lbs,body) ->
             let uu____13216 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13216)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13250 =
                let uu____13251 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13251  in
              FStar_All.pipe_left wrap uu____13250
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13258 =
                let uu____13259 =
                  let uu____13272 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13288 = pack_pat p1  in
                         (uu____13288, false)) ps
                     in
                  (fv, uu____13272)  in
                FStar_Syntax_Syntax.Pat_cons uu____13259  in
              FStar_All.pipe_left wrap uu____13258
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
            (fun uu___356_13334  ->
               match uu___356_13334 with
               | (pat,t1) ->
                   let uu____13351 = pack_pat pat  in
                   (uu____13351, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13399 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13399
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13427 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13427
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13473 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13473
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13512 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13512
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13529 =
        bind get
          (fun ps  ->
             let uu____13535 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13535 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13529
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13564 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___426_13571 = ps  in
                 let uu____13572 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___426_13571.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___426_13571.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___426_13571.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___426_13571.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___426_13571.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___426_13571.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___426_13571.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___426_13571.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___426_13571.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___426_13571.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___426_13571.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___426_13571.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13572
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13564
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13597 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13597 with
      | (u,ctx_uvars,g_u) ->
          let uu____13629 = FStar_List.hd ctx_uvars  in
          (match uu____13629 with
           | (ctx_uvar,uu____13643) ->
               let g =
                 let uu____13645 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13645 false
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
        let uu____13665 = goal_of_goal_ty env typ  in
        match uu____13665 with
        | (g,g_u) ->
            let ps =
              let uu____13677 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13678 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13677;
                FStar_Tactics_Types.local_state = uu____13678
              }  in
            let uu____13685 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13685)
  