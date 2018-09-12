open Prims
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
        (try (fun uu___359_158  -> match () with | () -> run t p) ()
         with | uu___358_162 -> FStar_Tactics_Result.Failed (uu___358_162, p))
  
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
           let uu____236 = run t1 p  in
           match uu____236 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____243 = t2 a  in run uu____243 q
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
    let uu____263 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____263 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____281 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____282 =
      let uu____283 = check_goal_solved g  in
      match uu____283 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____287 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____287
       in
    FStar_Util.format2 "%s%s\n" uu____281 uu____282
  
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
          let w =
            let uu____321 = FStar_Options.print_implicits ()  in
            if uu____321
            then
              let uu____322 = FStar_Tactics_Types.goal_env g  in
              let uu____323 = FStar_Tactics_Types.goal_witness g  in
              tts uu____322 uu____323
            else
              (let uu____325 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____325 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____329 = FStar_Tactics_Types.goal_env g  in
                   let uu____330 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____329 uu____330)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____342 = FStar_Util.string_of_int i  in
                let uu____343 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____342 uu____343
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.strcat " (" (Prims.strcat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____348 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____349 =
                 let uu____350 = FStar_Tactics_Types.goal_env g  in
                 tts uu____350
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____348 w uu____349)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____366 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____366
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____382 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____382
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____403 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____403
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____410) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____420) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____439 =
      let uu____440 = FStar_Tactics_Types.goal_env g  in
      let uu____441 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____440 uu____441  in
    FStar_Syntax_Util.un_squash uu____439
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____447 = get_phi g  in FStar_Option.isSome uu____447 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____466  ->
    bind get
      (fun ps  ->
         let uu____472 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____472)
  
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
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____507 =
          let uu____510 =
            let uu____513 =
              let uu____514 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____514
                msg
               in
            let uu____515 =
              let uu____518 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____519 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____519
                else ""  in
              let uu____521 =
                let uu____524 =
                  let uu____525 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____525
                  then
                    let uu____526 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____526
                  else ""  in
                [uu____524]  in
              uu____518 :: uu____521  in
            uu____513 :: uu____515  in
          let uu____528 =
            let uu____531 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____542 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____531 uu____542  in
          FStar_List.append uu____510 uu____528  in
        FStar_String.concat "" uu____507
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____563 =
        let uu____564 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____564  in
      let uu____565 =
        let uu____570 =
          let uu____571 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____571  in
        FStar_Syntax_Print.binders_to_json uu____570  in
      FStar_All.pipe_right uu____563 uu____565  in
    let uu____572 =
      let uu____579 =
        let uu____586 =
          let uu____591 =
            let uu____592 =
              let uu____599 =
                let uu____604 =
                  let uu____605 =
                    let uu____606 = FStar_Tactics_Types.goal_env g  in
                    let uu____607 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____606 uu____607  in
                  FStar_Util.JsonStr uu____605  in
                ("witness", uu____604)  in
              let uu____608 =
                let uu____615 =
                  let uu____620 =
                    let uu____621 =
                      let uu____622 = FStar_Tactics_Types.goal_env g  in
                      let uu____623 = FStar_Tactics_Types.goal_type g  in
                      tts uu____622 uu____623  in
                    FStar_Util.JsonStr uu____621  in
                  ("type", uu____620)  in
                [uu____615;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____599 :: uu____608  in
            FStar_Util.JsonAssoc uu____592  in
          ("goal", uu____591)  in
        [uu____586]  in
      ("hyps", g_binders) :: uu____579  in
    FStar_Util.JsonAssoc uu____572
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____660  ->
    match uu____660 with
    | (msg,ps) ->
        let uu____667 =
          let uu____674 =
            let uu____681 =
              let uu____688 =
                let uu____695 =
                  let uu____700 =
                    let uu____701 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____701  in
                  ("goals", uu____700)  in
                let uu____704 =
                  let uu____711 =
                    let uu____716 =
                      let uu____717 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____717  in
                    ("smt-goals", uu____716)  in
                  [uu____711]  in
                uu____695 :: uu____704  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____688
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____681  in
          let uu____740 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____753 =
                let uu____758 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____758)  in
              [uu____753]
            else []  in
          FStar_List.append uu____674 uu____740  in
        FStar_Util.JsonAssoc uu____667
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____788  ->
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
         (let uu____811 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____811 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____879 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____879
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____887 . Prims.string -> Prims.string -> 'Auu____887 tac =
  fun msg  ->
    fun x  -> let uu____900 = FStar_Util.format1 msg x  in fail uu____900
  
let fail2 :
  'Auu____909 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____909 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____927 = FStar_Util.format2 msg x y  in fail uu____927
  
let fail3 :
  'Auu____938 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____938 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____961 = FStar_Util.format3 msg x y z  in fail uu____961
  
let fail4 :
  'Auu____974 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____974 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1002 = FStar_Util.format4 msg x y z w  in
            fail uu____1002
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1035 = run t ps  in
         match uu____1035 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___360_1059 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___360_1059.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___360_1059.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___360_1059.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___360_1059.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___360_1059.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___360_1059.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___360_1059.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___360_1059.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___360_1059.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___360_1059.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___360_1059.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___360_1059.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1097 = run t ps  in
         match uu____1097 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1144 = catch t  in
    bind uu____1144
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1171 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___362_1202  ->
              match () with
              | () -> let uu____1207 = trytac t  in run uu____1207 ps) ()
         with
         | FStar_Errors.Err (uu____1223,msg) ->
             (log ps
                (fun uu____1227  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1232,msg,uu____1234) ->
             (log ps
                (fun uu____1237  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1270 = run t ps  in
           match uu____1270 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg,q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.strcat pref (Prims.strcat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e,q) ->
               FStar_Tactics_Result.Failed (e, q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1291  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___363_1305 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_1305.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_1305.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___363_1305.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___363_1305.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_1305.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_1305.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_1305.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_1305.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___363_1305.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___363_1305.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_1305.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___363_1305.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1326 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1326
         then
           let uu____1327 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1328 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1327
             uu____1328
         else ());
        (try
           (fun uu___365_1335  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1342 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1342
                    then
                      let uu____1343 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1344 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1345 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1343
                        uu____1344 uu____1345
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1350 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1350 (fun uu____1354  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1361,msg) ->
             mlog
               (fun uu____1364  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1366  -> ret false)
         | FStar_Errors.Error (uu____1367,msg,r) ->
             mlog
               (fun uu____1372  ->
                  let uu____1373 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1373) (fun uu____1375  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___366_1386 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___366_1386.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___366_1386.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___366_1386.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___367_1389 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___367_1389.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___367_1389.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___367_1389.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___367_1389.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___367_1389.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___367_1389.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___367_1389.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___367_1389.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___367_1389.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___367_1389.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___367_1389.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___367_1389.FStar_Tactics_Types.local_state)
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
          (fun uu____1412  ->
             (let uu____1414 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1414
              then
                (FStar_Options.push ();
                 (let uu____1416 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1418 = __do_unify env t1 t2  in
              bind uu____1418
                (fun r  ->
                   (let uu____1425 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1425 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1428  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___368_1435 = ps  in
         let uu____1436 =
           FStar_List.filter
             (fun g  ->
                let uu____1442 = check_goal_solved g  in
                FStar_Option.isNone uu____1442) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___368_1435.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___368_1435.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___368_1435.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1436;
           FStar_Tactics_Types.smt_goals =
             (uu___368_1435.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___368_1435.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___368_1435.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___368_1435.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___368_1435.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___368_1435.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___368_1435.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___368_1435.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___368_1435.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1459 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1459 with
      | FStar_Pervasives_Native.Some uu____1464 ->
          let uu____1465 =
            let uu____1466 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1466  in
          fail uu____1465
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1482 = FStar_Tactics_Types.goal_env goal  in
      let uu____1483 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1482 solution uu____1483
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1489 =
         let uu___369_1490 = p  in
         let uu____1491 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___369_1490.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___369_1490.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___369_1490.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1491;
           FStar_Tactics_Types.smt_goals =
             (uu___369_1490.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___369_1490.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___369_1490.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___369_1490.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___369_1490.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___369_1490.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___369_1490.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___369_1490.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___369_1490.FStar_Tactics_Types.local_state)
         }  in
       set uu____1489)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1512  ->
           let uu____1513 =
             let uu____1514 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1514  in
           let uu____1515 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1513 uu____1515)
        (fun uu____1518  ->
           let uu____1519 = trysolve goal solution  in
           bind uu____1519
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1527  -> remove_solved_goals)
                else
                  (let uu____1529 =
                     let uu____1530 =
                       let uu____1531 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1531 solution  in
                     let uu____1532 =
                       let uu____1533 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1534 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1533 uu____1534  in
                     let uu____1535 =
                       let uu____1536 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1537 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1536 uu____1537  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1530 uu____1532 uu____1535
                      in
                   fail uu____1529)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1552 = set_solution goal solution  in
      bind uu____1552
        (fun uu____1556  ->
           bind __dismiss (fun uu____1558  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___370_1576 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1576.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1576.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1576.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___370_1576.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1576.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1576.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1576.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1576.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1576.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1576.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1576.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1576.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___371_1594 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1594.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1594.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1594.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1594.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___371_1594.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1594.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1594.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1594.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1594.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1594.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1594.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1594.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1615 = FStar_Options.defensive ()  in
    if uu____1615
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1620 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1620)
         in
      let b2 =
        b1 &&
          (let uu____1623 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1623)
         in
      let rec aux b3 e =
        let uu____1635 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1635 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1653 =
        (let uu____1656 = aux b2 env  in Prims.op_Negation uu____1656) &&
          (let uu____1658 = FStar_ST.op_Bang nwarn  in
           uu____1658 < (Prims.parse_int "5"))
         in
      (if uu____1653
       then
         ((let uu____1679 =
             let uu____1680 = FStar_Tactics_Types.goal_type g  in
             uu____1680.FStar_Syntax_Syntax.pos  in
           let uu____1683 =
             let uu____1688 =
               let uu____1689 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1689
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1688)  in
           FStar_Errors.log_issue uu____1679 uu____1683);
          (let uu____1690 =
             let uu____1691 = FStar_ST.op_Bang nwarn  in
             uu____1691 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1690))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___372_1751 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1751.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1751.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_1751.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___372_1751.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_1751.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1751.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1751.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1751.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_1751.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_1751.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_1751.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_1751.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___373_1771 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___373_1771.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___373_1771.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___373_1771.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___373_1771.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___373_1771.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___373_1771.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___373_1771.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___373_1771.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___373_1771.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___373_1771.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___373_1771.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___373_1771.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___374_1791 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_1791.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_1791.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___374_1791.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___374_1791.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___374_1791.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_1791.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_1791.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_1791.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___374_1791.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___374_1791.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_1791.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_1791.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___375_1811 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___375_1811.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___375_1811.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___375_1811.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___375_1811.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___375_1811.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___375_1811.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___375_1811.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___375_1811.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___375_1811.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___375_1811.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___375_1811.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___375_1811.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1822  -> add_goals [g]) 
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
        let uu____1850 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1850 with
        | (u,ctx_uvar,g_u) ->
            let uu____1884 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1884
              (fun uu____1893  ->
                 let uu____1894 =
                   let uu____1899 =
                     let uu____1900 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1900  in
                   (u, uu____1899)  in
                 ret uu____1894)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1918 = FStar_Syntax_Util.un_squash t  in
    match uu____1918 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1928 =
          let uu____1929 = FStar_Syntax_Subst.compress t'  in
          uu____1929.FStar_Syntax_Syntax.n  in
        (match uu____1928 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1933 -> false)
    | uu____1934 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1944 = FStar_Syntax_Util.un_squash t  in
    match uu____1944 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1954 =
          let uu____1955 = FStar_Syntax_Subst.compress t'  in
          uu____1955.FStar_Syntax_Syntax.n  in
        (match uu____1954 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1959 -> false)
    | uu____1960 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1971  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1982 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1982 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1989 = goal_to_string_verbose hd1  in
                    let uu____1990 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1989 uu____1990);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2000 =
      bind get
        (fun ps  ->
           let uu____2006 = cur_goal ()  in
           bind uu____2006
             (fun g  ->
                (let uu____2013 =
                   let uu____2014 = FStar_Tactics_Types.goal_type g  in
                   uu____2014.FStar_Syntax_Syntax.pos  in
                 let uu____2017 =
                   let uu____2022 =
                     let uu____2023 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2023
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2022)  in
                 FStar_Errors.log_issue uu____2013 uu____2017);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2000
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2038  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___376_2048 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___376_2048.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___376_2048.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___376_2048.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___376_2048.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___376_2048.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___376_2048.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___376_2048.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___376_2048.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___376_2048.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___376_2048.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___376_2048.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___376_2048.FStar_Tactics_Types.local_state)
           }  in
         let uu____2049 = set ps1  in
         bind uu____2049
           (fun uu____2054  ->
              let uu____2055 = FStar_BigInt.of_int_fs n1  in ret uu____2055))
  
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
              let uu____2088 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2088 phi  in
            let uu____2089 = new_uvar reason env typ  in
            bind uu____2089
              (fun uu____2104  ->
                 match uu____2104 with
                 | (uu____2111,ctx_uvar) ->
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
             (fun uu____2156  ->
                let uu____2157 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2157)
             (fun uu____2160  ->
                let e1 =
                  let uu___377_2162 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___377_2162.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___377_2162.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___377_2162.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___377_2162.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___377_2162.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___377_2162.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___377_2162.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___377_2162.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___377_2162.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___377_2162.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___377_2162.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___377_2162.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___377_2162.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___377_2162.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___377_2162.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___377_2162.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___377_2162.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___377_2162.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___377_2162.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___377_2162.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___377_2162.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___377_2162.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___377_2162.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___377_2162.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___377_2162.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___377_2162.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___377_2162.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___377_2162.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___377_2162.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___377_2162.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___377_2162.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___377_2162.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___377_2162.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___377_2162.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___377_2162.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___377_2162.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___377_2162.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___377_2162.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___377_2162.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___377_2162.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___377_2162.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___377_2162.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___379_2173  ->
                     match () with
                     | () ->
                         let uu____2182 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2182) ()
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
             (fun uu____2274  ->
                let uu____2275 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2275)
             (fun uu____2278  ->
                let e1 =
                  let uu___380_2280 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___380_2280.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___380_2280.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___380_2280.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___380_2280.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___380_2280.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___380_2280.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___380_2280.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___380_2280.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___380_2280.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___380_2280.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___380_2280.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___380_2280.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___380_2280.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___380_2280.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___380_2280.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___380_2280.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___380_2280.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___380_2280.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___380_2280.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___380_2280.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___380_2280.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___380_2280.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___380_2280.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___380_2280.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___380_2280.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___380_2280.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___380_2280.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___380_2280.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___380_2280.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___380_2280.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___380_2280.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___380_2280.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___380_2280.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___380_2280.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___380_2280.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___380_2280.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___380_2280.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___380_2280.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___380_2280.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___380_2280.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___380_2280.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___380_2280.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___382_2294  ->
                     match () with
                     | () ->
                         let uu____2303 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2303 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2341,msg) ->
                    let uu____2343 = tts e1 t  in
                    let uu____2344 =
                      let uu____2345 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2345
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2343 uu____2344 msg
                | FStar_Errors.Error (uu____2352,msg,uu____2354) ->
                    let uu____2355 = tts e1 t  in
                    let uu____2356 =
                      let uu____2357 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2357
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2355 uu____2356 msg))
  
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
             (fun uu____2406  ->
                let uu____2407 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2407)
             (fun uu____2411  ->
                let e1 =
                  let uu___383_2413 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___383_2413.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___383_2413.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___383_2413.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___383_2413.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___383_2413.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___383_2413.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___383_2413.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___383_2413.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___383_2413.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___383_2413.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___383_2413.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___383_2413.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___383_2413.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___383_2413.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___383_2413.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___383_2413.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___383_2413.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___383_2413.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___383_2413.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___383_2413.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___383_2413.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___383_2413.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___383_2413.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___383_2413.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___383_2413.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___383_2413.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___383_2413.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___383_2413.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___383_2413.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___383_2413.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___383_2413.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___383_2413.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___383_2413.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___383_2413.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___383_2413.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___383_2413.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___383_2413.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___383_2413.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___383_2413.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___383_2413.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___383_2413.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___383_2413.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___384_2415 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___384_2415.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___384_2415.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___384_2415.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___384_2415.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___384_2415.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___384_2415.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___384_2415.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___384_2415.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___384_2415.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___384_2415.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___384_2415.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___384_2415.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___384_2415.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___384_2415.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___384_2415.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___384_2415.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___384_2415.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___384_2415.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___384_2415.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___384_2415.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___384_2415.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___384_2415.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___384_2415.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___384_2415.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___384_2415.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___384_2415.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___384_2415.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___384_2415.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___384_2415.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___384_2415.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___384_2415.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___384_2415.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___384_2415.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___384_2415.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___384_2415.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___384_2415.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___384_2415.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___384_2415.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___384_2415.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___384_2415.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___384_2415.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___384_2415.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___386_2429  ->
                     match () with
                     | () ->
                         let uu____2438 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2438 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2476,msg) ->
                    let uu____2478 = tts e2 t  in
                    let uu____2479 =
                      let uu____2480 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2480
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2478 uu____2479 msg
                | FStar_Errors.Error (uu____2487,msg,uu____2489) ->
                    let uu____2490 = tts e2 t  in
                    let uu____2491 =
                      let uu____2492 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2492
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2490 uu____2491 msg))
  
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
  fun uu____2519  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___387_2537 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___387_2537.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___387_2537.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___387_2537.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___387_2537.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___387_2537.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___387_2537.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___387_2537.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___387_2537.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___387_2537.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___387_2537.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___387_2537.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___387_2537.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2561 = get_guard_policy ()  in
      bind uu____2561
        (fun old_pol  ->
           let uu____2567 = set_guard_policy pol  in
           bind uu____2567
             (fun uu____2571  ->
                bind t
                  (fun r  ->
                     let uu____2575 = set_guard_policy old_pol  in
                     bind uu____2575 (fun uu____2579  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2582 = let uu____2587 = cur_goal ()  in trytac uu____2587  in
  bind uu____2582
    (fun uu___350_2594  ->
       match uu___350_2594 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2600 = FStar_Options.peek ()  in ret uu____2600)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2622  ->
             let uu____2623 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2623)
          (fun uu____2626  ->
             let uu____2627 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2627
               (fun uu____2631  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2635 =
                         let uu____2636 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2636.FStar_TypeChecker_Env.guard_f  in
                       match uu____2635 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2640 = istrivial e f  in
                           if uu____2640
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2650 =
                                          let uu____2655 =
                                            let uu____2656 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2656
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2655)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2650);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2659  ->
                                           let uu____2660 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2660)
                                        (fun uu____2663  ->
                                           let uu____2664 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2664
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___388_2671 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___388_2671.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___388_2671.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___388_2671.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___388_2671.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2674  ->
                                           let uu____2675 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2675)
                                        (fun uu____2678  ->
                                           let uu____2679 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2679
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___389_2686 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___389_2686.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___389_2686.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___389_2686.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___389_2686.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2689  ->
                                           let uu____2690 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2690)
                                        (fun uu____2692  ->
                                           try
                                             (fun uu___391_2697  ->
                                                match () with
                                                | () ->
                                                    let uu____2700 =
                                                      let uu____2701 =
                                                        let uu____2702 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2702
                                                         in
                                                      Prims.op_Negation
                                                        uu____2701
                                                       in
                                                    if uu____2700
                                                    then
                                                      mlog
                                                        (fun uu____2707  ->
                                                           let uu____2708 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2708)
                                                        (fun uu____2710  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___390_2713 ->
                                               mlog
                                                 (fun uu____2718  ->
                                                    let uu____2719 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2719)
                                                 (fun uu____2721  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2731 =
      let uu____2734 = cur_goal ()  in
      bind uu____2734
        (fun goal  ->
           let uu____2740 =
             let uu____2749 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____2749 t  in
           bind uu____2740
             (fun uu____2760  ->
                match uu____2760 with
                | (uu____2769,typ,uu____2771) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2731
  
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
            let uu____2805 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____2805 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2816  ->
    let uu____2819 = cur_goal ()  in
    bind uu____2819
      (fun goal  ->
         let uu____2825 =
           let uu____2826 = FStar_Tactics_Types.goal_env goal  in
           let uu____2827 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2826 uu____2827  in
         if uu____2825
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2831 =
              let uu____2832 = FStar_Tactics_Types.goal_env goal  in
              let uu____2833 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2832 uu____2833  in
            fail1 "Not a trivial goal: %s" uu____2831))
  
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
             let uu____2882 =
               try
                 (fun uu___396_2905  ->
                    match () with
                    | () ->
                        let uu____2916 =
                          let uu____2925 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2925
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2916) ()
               with | uu___395_2935 -> fail "divide: not enough goals"  in
             bind uu____2882
               (fun uu____2971  ->
                  match uu____2971 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___392_2997 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___392_2997.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___392_2997.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___392_2997.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___392_2997.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___392_2997.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___392_2997.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___392_2997.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___392_2997.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___392_2997.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___392_2997.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___392_2997.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2998 = set lp  in
                      bind uu____2998
                        (fun uu____3006  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___393_3022 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___393_3022.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___393_3022.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___393_3022.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___393_3022.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___393_3022.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___393_3022.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___393_3022.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___393_3022.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___393_3022.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___393_3022.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___393_3022.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3023 = set rp  in
                                     bind uu____3023
                                       (fun uu____3031  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___394_3047 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___394_3047.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___394_3047.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3048 = set p'
                                                       in
                                                    bind uu____3048
                                                      (fun uu____3056  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3062 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3083 = divide FStar_BigInt.one f idtac  in
    bind uu____3083
      (fun uu____3096  -> match uu____3096 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3133::uu____3134 ->
             let uu____3137 =
               let uu____3146 = map tau  in
               divide FStar_BigInt.one tau uu____3146  in
             bind uu____3137
               (fun uu____3164  ->
                  match uu____3164 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3205 =
        bind t1
          (fun uu____3210  ->
             let uu____3211 = map t2  in
             bind uu____3211 (fun uu____3219  -> ret ()))
         in
      focus uu____3205
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3228  ->
    let uu____3231 =
      let uu____3234 = cur_goal ()  in
      bind uu____3234
        (fun goal  ->
           let uu____3243 =
             let uu____3250 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3250  in
           match uu____3243 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3259 =
                 let uu____3260 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3260  in
               if uu____3259
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3265 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3265 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3279 = new_uvar "intro" env' typ'  in
                  bind uu____3279
                    (fun uu____3295  ->
                       match uu____3295 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3319 = set_solution goal sol  in
                           bind uu____3319
                             (fun uu____3325  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3327 =
                                  let uu____3330 = bnorm_goal g  in
                                  replace_cur uu____3330  in
                                bind uu____3327 (fun uu____3332  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3337 =
                 let uu____3338 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3339 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3338 uu____3339  in
               fail1 "goal is not an arrow (%s)" uu____3337)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3231
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3354  ->
    let uu____3361 = cur_goal ()  in
    bind uu____3361
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3378 =
            let uu____3385 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3385  in
          match uu____3378 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3398 =
                let uu____3399 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3399  in
              if uu____3398
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3412 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3412
                    in
                 let bs =
                   let uu____3422 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3422; b]  in
                 let env' =
                   let uu____3448 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3448 bs  in
                 let uu____3449 =
                   let uu____3456 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3456  in
                 bind uu____3449
                   (fun uu____3475  ->
                      match uu____3475 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3489 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3492 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3489
                              FStar_Parser_Const.effect_Tot_lid uu____3492 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3510 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3510 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3532 =
                                   let uu____3533 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3533.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3532
                                  in
                               let uu____3546 = set_solution goal tm  in
                               bind uu____3546
                                 (fun uu____3555  ->
                                    let uu____3556 =
                                      let uu____3559 =
                                        bnorm_goal
                                          (let uu___397_3562 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___397_3562.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___397_3562.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___397_3562.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___397_3562.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____3559  in
                                    bind uu____3556
                                      (fun uu____3569  ->
                                         let uu____3570 =
                                           let uu____3575 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3575, b)  in
                                         ret uu____3570)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3584 =
                let uu____3585 = FStar_Tactics_Types.goal_env goal  in
                let uu____3586 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3585 uu____3586  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3584))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3604 = cur_goal ()  in
    bind uu____3604
      (fun goal  ->
         mlog
           (fun uu____3611  ->
              let uu____3612 =
                let uu____3613 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3613  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3612)
           (fun uu____3618  ->
              let steps =
                let uu____3622 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3622
                 in
              let t =
                let uu____3626 = FStar_Tactics_Types.goal_env goal  in
                let uu____3627 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3626 uu____3627  in
              let uu____3628 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3628))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3652 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____3660 -> g.FStar_Tactics_Types.opts
                 | uu____3663 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____3668  ->
                    let uu____3669 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3669)
                 (fun uu____3672  ->
                    let uu____3673 = __tc_lax e t  in
                    bind uu____3673
                      (fun uu____3694  ->
                         match uu____3694 with
                         | (t1,uu____3704,uu____3705) ->
                             let steps =
                               let uu____3709 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3709
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____3715  ->
                                  let uu____3716 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3716)
                               (fun uu____3718  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3652
  
let (refine_intro : unit -> unit tac) =
  fun uu____3729  ->
    let uu____3732 =
      let uu____3735 = cur_goal ()  in
      bind uu____3735
        (fun g  ->
           let uu____3742 =
             let uu____3753 = FStar_Tactics_Types.goal_env g  in
             let uu____3754 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3753 uu____3754
              in
           match uu____3742 with
           | (uu____3757,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3782 =
                 let uu____3787 =
                   let uu____3792 =
                     let uu____3793 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3793]  in
                   FStar_Syntax_Subst.open_term uu____3792 phi  in
                 match uu____3787 with
                 | (bvs,phi1) ->
                     let uu____3818 =
                       let uu____3819 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3819  in
                     (uu____3818, phi1)
                  in
               (match uu____3782 with
                | (bv1,phi1) ->
                    let uu____3838 =
                      let uu____3841 = FStar_Tactics_Types.goal_env g  in
                      let uu____3842 =
                        let uu____3843 =
                          let uu____3846 =
                            let uu____3847 =
                              let uu____3854 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3854)  in
                            FStar_Syntax_Syntax.NT uu____3847  in
                          [uu____3846]  in
                        FStar_Syntax_Subst.subst uu____3843 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3841
                        uu____3842 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____3838
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3862  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3732
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3881 = cur_goal ()  in
      bind uu____3881
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3889 = FStar_Tactics_Types.goal_env goal  in
               let uu____3890 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3889 uu____3890
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3892 = __tc env t  in
           bind uu____3892
             (fun uu____3911  ->
                match uu____3911 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3926  ->
                         let uu____3927 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3928 =
                           let uu____3929 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3929
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3927 uu____3928)
                      (fun uu____3932  ->
                         let uu____3933 =
                           let uu____3936 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3936 guard  in
                         bind uu____3933
                           (fun uu____3938  ->
                              mlog
                                (fun uu____3942  ->
                                   let uu____3943 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3944 =
                                     let uu____3945 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3945
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3943 uu____3944)
                                (fun uu____3948  ->
                                   let uu____3949 =
                                     let uu____3952 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3953 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3952 typ uu____3953  in
                                   bind uu____3949
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3959 =
                                             let uu____3960 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3960 t1  in
                                           let uu____3961 =
                                             let uu____3962 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3962 typ  in
                                           let uu____3963 =
                                             let uu____3964 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3965 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3964 uu____3965  in
                                           let uu____3966 =
                                             let uu____3967 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3968 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3967 uu____3968  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3959 uu____3961 uu____3963
                                             uu____3966)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3988 =
          mlog
            (fun uu____3993  ->
               let uu____3994 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3994)
            (fun uu____3997  ->
               let uu____3998 =
                 let uu____4005 = __exact_now set_expected_typ1 tm  in
                 catch uu____4005  in
               bind uu____3998
                 (fun uu___352_4014  ->
                    match uu___352_4014 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4025  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4028  ->
                             let uu____4029 =
                               let uu____4036 =
                                 let uu____4039 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4039
                                   (fun uu____4044  ->
                                      let uu____4045 = refine_intro ()  in
                                      bind uu____4045
                                        (fun uu____4049  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4036  in
                             bind uu____4029
                               (fun uu___351_4056  ->
                                  match uu___351_4056 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4065  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4067  -> ret ())
                                  | FStar_Util.Inl uu____4068 ->
                                      mlog
                                        (fun uu____4070  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4072  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3988
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4122 = f x  in
          bind uu____4122
            (fun y  ->
               let uu____4130 = mapM f xs  in
               bind uu____4130 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4201 = do_unify e ty1 ty2  in
          bind uu____4201
            (fun uu___353_4213  ->
               if uu___353_4213
               then ret acc
               else
                 (let uu____4232 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4232 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4253 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4254 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4253
                        uu____4254
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4269 =
                        let uu____4270 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4270  in
                      if uu____4269
                      then fail "Codomain is effectful"
                      else
                        (let uu____4290 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4290
                           (fun uu____4316  ->
                              match uu____4316 with
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
      let uu____4402 =
        mlog
          (fun uu____4407  ->
             let uu____4408 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4408)
          (fun uu____4411  ->
             let uu____4412 = cur_goal ()  in
             bind uu____4412
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4420 = __tc e tm  in
                  bind uu____4420
                    (fun uu____4441  ->
                       match uu____4441 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4454 =
                             let uu____4465 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4465  in
                           bind uu____4454
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4508  ->
                                       fun w  ->
                                         match uu____4508 with
                                         | (uvt,q,uu____4526) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4558 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4575  ->
                                       fun s  ->
                                         match uu____4575 with
                                         | (uu____4587,uu____4588,uv) ->
                                             let uu____4590 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4590) uvs uu____4558
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4599 = solve' goal w  in
                                bind uu____4599
                                  (fun uu____4604  ->
                                     let uu____4605 =
                                       mapM
                                         (fun uu____4622  ->
                                            match uu____4622 with
                                            | (uvt,q,uv) ->
                                                let uu____4634 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4634 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4639 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4640 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4640
                                                     then ret ()
                                                     else
                                                       (let uu____4644 =
                                                          let uu____4647 =
                                                            bnorm_goal
                                                              (let uu___398_4650
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___398_4650.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___398_4650.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___398_4650.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____4647]  in
                                                        add_goals uu____4644)))
                                         uvs
                                        in
                                     bind uu____4605
                                       (fun uu____4654  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4402
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4679 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4679
    then
      let uu____4686 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4701 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4754 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4686 with
      | (pre,post) ->
          let post1 =
            let uu____4786 =
              let uu____4797 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4797]  in
            FStar_Syntax_Util.mk_app post uu____4786  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4827 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4827
       then
         let uu____4834 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4834
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4867 =
      let uu____4870 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4877  ->
                  let uu____4878 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4878)
               (fun uu____4882  ->
                  let is_unit_t t =
                    let uu____4889 =
                      let uu____4890 = FStar_Syntax_Subst.compress t  in
                      uu____4890.FStar_Syntax_Syntax.n  in
                    match uu____4889 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4894 -> false  in
                  let uu____4895 = cur_goal ()  in
                  bind uu____4895
                    (fun goal  ->
                       let uu____4901 =
                         let uu____4910 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4910 tm  in
                       bind uu____4901
                         (fun uu____4925  ->
                            match uu____4925 with
                            | (tm1,t,guard) ->
                                let uu____4937 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4937 with
                                 | (bs,comp) ->
                                     let uu____4970 = lemma_or_sq comp  in
                                     (match uu____4970 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4989 =
                                            FStar_List.fold_left
                                              (fun uu____5037  ->
                                                 fun uu____5038  ->
                                                   match (uu____5037,
                                                           uu____5038)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5151 =
                                                         is_unit_t b_t  in
                                                       if uu____5151
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5189 =
                                                            let uu____5202 =
                                                              let uu____5203
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5203.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5206 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5202
                                                              uu____5206 b_t
                                                             in
                                                          match uu____5189
                                                          with
                                                          | (u,uu____5224,g_u)
                                                              ->
                                                              let uu____5238
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5238,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4989 with
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
                                               let uu____5317 =
                                                 let uu____5320 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5321 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5322 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5320
                                                   uu____5321 uu____5322
                                                  in
                                               bind uu____5317
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5330 =
                                                        let uu____5331 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5331 tm1
                                                         in
                                                      let uu____5332 =
                                                        let uu____5333 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5334 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5333
                                                          uu____5334
                                                         in
                                                      let uu____5335 =
                                                        let uu____5336 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5337 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5336
                                                          uu____5337
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5330 uu____5332
                                                        uu____5335
                                                    else
                                                      (let uu____5339 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5339
                                                         (fun uu____5344  ->
                                                            let uu____5345 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5345
                                                              (fun uu____5353
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5378
                                                                    =
                                                                    let uu____5381
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5381
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5378
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
                                                                    let uu____5416
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5416)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5432
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5432
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5450)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5476)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5493
                                                                    -> false)
                                                                    in
                                                                 let uu____5494
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
                                                                    let uu____5524
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5524
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5546)
                                                                    ->
                                                                    let uu____5571
                                                                    =
                                                                    let uu____5572
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5572.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5571
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5580)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___399_5600
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___399_5600.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___399_5600.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___399_5600.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___399_5600.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5603
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5609
                                                                     ->
                                                                    let uu____5610
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5611
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5610
                                                                    uu____5611)
                                                                    (fun
                                                                    uu____5616
                                                                     ->
                                                                    let env =
                                                                    let uu___400_5618
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___400_5618.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5620
                                                                    =
                                                                    let uu____5623
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5624
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5625
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5624
                                                                    uu____5625
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5627
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5623
                                                                    uu____5627
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5620
                                                                    (fun
                                                                    uu____5631
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5494
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
                                                                    let uu____5693
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5693
                                                                    then
                                                                    let uu____5696
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5696
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
                                                                    let uu____5710
                                                                    =
                                                                    let uu____5711
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5711
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5710)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5712
                                                                    =
                                                                    let uu____5715
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5715
                                                                    guard  in
                                                                    bind
                                                                    uu____5712
                                                                    (fun
                                                                    uu____5718
                                                                     ->
                                                                    let uu____5719
                                                                    =
                                                                    let uu____5722
                                                                    =
                                                                    let uu____5723
                                                                    =
                                                                    let uu____5724
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5725
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5724
                                                                    uu____5725
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5723
                                                                     in
                                                                    if
                                                                    uu____5722
                                                                    then
                                                                    let uu____5728
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5728
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5719
                                                                    (fun
                                                                    uu____5731
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4870  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4867
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5753 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5753 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5763::(e1,uu____5765)::(e2,uu____5767)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5828 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5852 = destruct_eq' typ  in
    match uu____5852 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5882 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5882 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____5950 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5950 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____6006 = aux e'  in
               FStar_Util.map_opt uu____6006
                 (fun uu____6037  ->
                    match uu____6037 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____6063 = aux e  in
      FStar_Util.map_opt uu____6063
        (fun uu____6094  ->
           match uu____6094 with
           | (e',bv,bvs) -> (e', bv, (FStar_List.rev bvs)))
  
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
          let uu____6166 =
            let uu____6177 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6177  in
          FStar_Util.map_opt uu____6166
            (fun uu____6195  ->
               match uu____6195 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___401_6217 = bv  in
                     let uu____6218 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___401_6217.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___401_6217.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6218
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___402_6226 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6227 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6236 =
                       let uu____6239 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6239  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___402_6226.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6227;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6236;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___402_6226.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___402_6226.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___402_6226.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___403_6240 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___403_6240.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___403_6240.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___403_6240.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___403_6240.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6250 =
      let uu____6253 = cur_goal ()  in
      bind uu____6253
        (fun goal  ->
           let uu____6261 = h  in
           match uu____6261 with
           | (bv,uu____6265) ->
               mlog
                 (fun uu____6273  ->
                    let uu____6274 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6275 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6274
                      uu____6275)
                 (fun uu____6278  ->
                    let uu____6279 =
                      let uu____6290 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6290  in
                    match uu____6279 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____6316 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____6316 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6331 =
                               let uu____6332 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6332.FStar_Syntax_Syntax.n  in
                             (match uu____6331 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___404_6349 = bv2  in
                                    let uu____6350 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___404_6349.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___404_6349.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6350
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___405_6358 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6359 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6368 =
                                      let uu____6371 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6371
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___405_6358.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6359;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6368;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___405_6358.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___405_6358.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___405_6358.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___406_6374 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___406_6374.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___406_6374.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___406_6374.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___406_6374.FStar_Tactics_Types.label)
                                     })
                              | uu____6375 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6376 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6250
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6401 =
        let uu____6404 = cur_goal ()  in
        bind uu____6404
          (fun goal  ->
             let uu____6415 = b  in
             match uu____6415 with
             | (bv,uu____6419) ->
                 let bv' =
                   let uu____6425 =
                     let uu___407_6426 = bv  in
                     let uu____6427 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6427;
                       FStar_Syntax_Syntax.index =
                         (uu___407_6426.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___407_6426.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6425  in
                 let s1 =
                   let uu____6431 =
                     let uu____6432 =
                       let uu____6439 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6439)  in
                     FStar_Syntax_Syntax.NT uu____6432  in
                   [uu____6431]  in
                 let uu____6444 = subst_goal bv bv' s1 goal  in
                 (match uu____6444 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6401
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6463 =
      let uu____6466 = cur_goal ()  in
      bind uu____6466
        (fun goal  ->
           let uu____6475 = b  in
           match uu____6475 with
           | (bv,uu____6479) ->
               let uu____6484 =
                 let uu____6495 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6495  in
               (match uu____6484 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____6521 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6521 with
                     | (ty,u) ->
                         let uu____6530 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6530
                           (fun uu____6548  ->
                              match uu____6548 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___408_6558 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___408_6558.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___408_6558.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6562 =
                                      let uu____6563 =
                                        let uu____6570 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____6570)  in
                                      FStar_Syntax_Syntax.NT uu____6563  in
                                    [uu____6562]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___409_6582 = b1  in
                                         let uu____6583 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___409_6582.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___409_6582.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6583
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6590  ->
                                       let new_goal =
                                         let uu____6592 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6593 =
                                           let uu____6594 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6594
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6592 uu____6593
                                          in
                                       let uu____6595 = add_goals [new_goal]
                                          in
                                       bind uu____6595
                                         (fun uu____6600  ->
                                            let uu____6601 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6601
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6463
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6624 =
        let uu____6627 = cur_goal ()  in
        bind uu____6627
          (fun goal  ->
             let uu____6636 = b  in
             match uu____6636 with
             | (bv,uu____6640) ->
                 let uu____6645 =
                   let uu____6656 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6656  in
                 (match uu____6645 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____6685 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6685
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___410_6690 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___410_6690.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___410_6690.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6692 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6692))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6624
  
let (revert : unit -> unit tac) =
  fun uu____6703  ->
    let uu____6706 = cur_goal ()  in
    bind uu____6706
      (fun goal  ->
         let uu____6712 =
           let uu____6719 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6719  in
         match uu____6712 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6735 =
                 let uu____6738 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6738  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6735
                in
             let uu____6753 = new_uvar "revert" env' typ'  in
             bind uu____6753
               (fun uu____6768  ->
                  match uu____6768 with
                  | (r,u_r) ->
                      let uu____6777 =
                        let uu____6780 =
                          let uu____6781 =
                            let uu____6782 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6782.FStar_Syntax_Syntax.pos  in
                          let uu____6785 =
                            let uu____6790 =
                              let uu____6791 =
                                let uu____6800 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6800  in
                              [uu____6791]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6790  in
                          uu____6785 FStar_Pervasives_Native.None uu____6781
                           in
                        set_solution goal uu____6780  in
                      bind uu____6777
                        (fun uu____6821  ->
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
      let uu____6833 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6833
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6848 = cur_goal ()  in
    bind uu____6848
      (fun goal  ->
         mlog
           (fun uu____6856  ->
              let uu____6857 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6858 =
                let uu____6859 =
                  let uu____6860 =
                    let uu____6869 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6869  in
                  FStar_All.pipe_right uu____6860 FStar_List.length  in
                FStar_All.pipe_right uu____6859 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6857 uu____6858)
           (fun uu____6886  ->
              let uu____6887 =
                let uu____6898 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6898  in
              match uu____6887 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6942 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6942
                        then
                          let uu____6945 =
                            let uu____6946 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6946
                             in
                          fail uu____6945
                        else check1 bvs2
                     in
                  let uu____6948 =
                    let uu____6949 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____6949  in
                  if uu____6948
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6953 = check1 bvs  in
                     bind uu____6953
                       (fun uu____6959  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6961 =
                            let uu____6968 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6968  in
                          bind uu____6961
                            (fun uu____6977  ->
                               match uu____6977 with
                               | (ut,uvar_ut) ->
                                   let uu____6986 = set_solution goal ut  in
                                   bind uu____6986
                                     (fun uu____6991  ->
                                        let uu____6992 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____6992))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6999  ->
    let uu____7002 = cur_goal ()  in
    bind uu____7002
      (fun goal  ->
         let uu____7008 =
           let uu____7015 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7015  in
         match uu____7008 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____7023) ->
             let uu____7028 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____7028)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____7038 = cur_goal ()  in
    bind uu____7038
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7048 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7048  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7051  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____7061 = cur_goal ()  in
    bind uu____7061
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7071 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7071  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7074  -> add_goals [g']))
  
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
            let uu____7114 = FStar_Syntax_Subst.compress t  in
            uu____7114.FStar_Syntax_Syntax.n  in
          let uu____7117 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___414_7123 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___414_7123.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___414_7123.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____7117
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7139 =
                   let uu____7140 = FStar_Syntax_Subst.compress t1  in
                   uu____7140.FStar_Syntax_Syntax.n  in
                 match uu____7139 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____7171 = ff hd1  in
                     bind uu____7171
                       (fun hd2  ->
                          let fa uu____7197 =
                            match uu____7197 with
                            | (a,q) ->
                                let uu____7218 = ff a  in
                                bind uu____7218 (fun a1  -> ret (a1, q))
                             in
                          let uu____7237 = mapM fa args  in
                          bind uu____7237
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7319 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7319 with
                      | (bs1,t') ->
                          let uu____7328 =
                            let uu____7331 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7331 t'  in
                          bind uu____7328
                            (fun t''  ->
                               let uu____7335 =
                                 let uu____7336 =
                                   let uu____7355 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7364 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7355, uu____7364, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7336  in
                               ret uu____7335))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7439 = ff hd1  in
                     bind uu____7439
                       (fun hd2  ->
                          let ffb br =
                            let uu____7454 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7454 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7486 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7486  in
                                let uu____7487 = ff1 e  in
                                bind uu____7487
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7502 = mapM ffb brs  in
                          bind uu____7502
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7546;
                          FStar_Syntax_Syntax.lbtyp = uu____7547;
                          FStar_Syntax_Syntax.lbeff = uu____7548;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7550;
                          FStar_Syntax_Syntax.lbpos = uu____7551;_}::[]),e)
                     ->
                     let lb =
                       let uu____7576 =
                         let uu____7577 = FStar_Syntax_Subst.compress t1  in
                         uu____7577.FStar_Syntax_Syntax.n  in
                       match uu____7576 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7581) -> lb
                       | uu____7594 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7603 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7603
                         (fun def1  ->
                            ret
                              (let uu___411_7609 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___411_7609.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___411_7609.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___411_7609.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___411_7609.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___411_7609.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___411_7609.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7610 = fflb lb  in
                     bind uu____7610
                       (fun lb1  ->
                          let uu____7620 =
                            let uu____7625 =
                              let uu____7626 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7626]  in
                            FStar_Syntax_Subst.open_term uu____7625 e  in
                          match uu____7620 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7656 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7656  in
                              let uu____7657 = ff1 e1  in
                              bind uu____7657
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7698 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7698
                         (fun def  ->
                            ret
                              (let uu___412_7704 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___412_7704.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___412_7704.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___412_7704.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___412_7704.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___412_7704.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___412_7704.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7705 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7705 with
                      | (lbs1,e1) ->
                          let uu____7720 = mapM fflb lbs1  in
                          bind uu____7720
                            (fun lbs2  ->
                               let uu____7732 = ff e1  in
                               bind uu____7732
                                 (fun e2  ->
                                    let uu____7740 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7740 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7808 = ff t2  in
                     bind uu____7808
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7839 = ff t2  in
                     bind uu____7839
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7846 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___413_7853 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___413_7853.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___413_7853.FStar_Syntax_Syntax.vars)
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
              let uu____7895 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___415_7904 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___415_7904.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___415_7904.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___415_7904.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___415_7904.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___415_7904.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___415_7904.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___415_7904.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___415_7904.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___415_7904.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___415_7904.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___415_7904.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___415_7904.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___415_7904.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___415_7904.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___415_7904.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___415_7904.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___415_7904.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___415_7904.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___415_7904.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___415_7904.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___415_7904.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___415_7904.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___415_7904.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___415_7904.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___415_7904.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___415_7904.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___415_7904.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___415_7904.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___415_7904.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___415_7904.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___415_7904.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___415_7904.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___415_7904.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___415_7904.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___415_7904.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___415_7904.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___415_7904.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___415_7904.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___415_7904.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___415_7904.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___415_7904.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___415_7904.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____7895 with
              | (t1,lcomp,g) ->
                  let uu____7910 =
                    (let uu____7913 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____7913) ||
                      (let uu____7915 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____7915)
                     in
                  if uu____7910
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____7923 = new_uvar "pointwise_rec" env typ  in
                       bind uu____7923
                         (fun uu____7939  ->
                            match uu____7939 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____7952  ->
                                      let uu____7953 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____7954 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____7953 uu____7954);
                                 (let uu____7955 =
                                    let uu____7958 =
                                      let uu____7959 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____7959 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____7958
                                      opts label1
                                     in
                                  bind uu____7955
                                    (fun uu____7962  ->
                                       let uu____7963 =
                                         bind tau
                                           (fun uu____7969  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____7975  ->
                                                   let uu____7976 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____7977 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____7976 uu____7977);
                                              ret ut1)
                                          in
                                       focus uu____7963))))
                        in
                     let uu____7978 = catch rewrite_eq  in
                     bind uu____7978
                       (fun x  ->
                          match x with
                          | FStar_Util.Inl (FStar_Tactics_Types.TacticFailure
                              "SKIP") -> ret t1
                          | FStar_Util.Inl e -> traise e
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
          let uu____8176 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____8176
            (fun t1  ->
               let uu____8184 =
                 f env
                   (let uu___418_8193 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___418_8193.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___418_8193.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____8184
                 (fun uu____8209  ->
                    match uu____8209 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____8232 =
                               let uu____8233 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____8233.FStar_Syntax_Syntax.n  in
                             match uu____8232 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8270 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8270
                                   (fun uu____8295  ->
                                      match uu____8295 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8311 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8311
                                            (fun uu____8338  ->
                                               match uu____8338 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___416_8368 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___416_8368.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___416_8368.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8410 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8410 with
                                  | (bs1,t') ->
                                      let uu____8425 =
                                        let uu____8432 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8432 ctrl1 t'
                                         in
                                      bind uu____8425
                                        (fun uu____8450  ->
                                           match uu____8450 with
                                           | (t'',ctrl2) ->
                                               let uu____8465 =
                                                 let uu____8472 =
                                                   let uu___417_8475 = t4  in
                                                   let uu____8478 =
                                                     let uu____8479 =
                                                       let uu____8498 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8507 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8498,
                                                         uu____8507, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8479
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8478;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___417_8475.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___417_8475.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8472, ctrl2)  in
                                               ret uu____8465))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8560 -> ret (t3, ctrl1))))

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
              let uu____8607 = ctrl_tac_fold f env ctrl t  in
              bind uu____8607
                (fun uu____8631  ->
                   match uu____8631 with
                   | (t1,ctrl1) ->
                       let uu____8646 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8646
                         (fun uu____8673  ->
                            match uu____8673 with
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
                let uu____8762 =
                  let uu____8769 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____8769
                    (fun uu____8778  ->
                       let uu____8779 = ctrl t1  in
                       bind uu____8779
                         (fun res  ->
                            let uu____8802 = trivial ()  in
                            bind uu____8802 (fun uu____8810  -> ret res)))
                   in
                bind uu____8762
                  (fun uu____8826  ->
                     match uu____8826 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____8850 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___419_8859 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___419_8859.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___419_8859.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___419_8859.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___419_8859.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___419_8859.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___419_8859.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___419_8859.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___419_8859.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___419_8859.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___419_8859.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___419_8859.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___419_8859.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___419_8859.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___419_8859.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___419_8859.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___419_8859.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___419_8859.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___419_8859.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___419_8859.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___419_8859.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___419_8859.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___419_8859.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___419_8859.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___419_8859.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___419_8859.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___419_8859.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___419_8859.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___419_8859.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___419_8859.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___419_8859.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___419_8859.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___419_8859.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___419_8859.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___419_8859.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___419_8859.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___419_8859.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___419_8859.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___419_8859.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___419_8859.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___419_8859.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___419_8859.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___419_8859.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____8850 with
                            | (t2,lcomp,g) ->
                                let uu____8869 =
                                  (let uu____8872 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____8872) ||
                                    (let uu____8874 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____8874)
                                   in
                                if uu____8869
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____8887 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____8887
                                     (fun uu____8907  ->
                                        match uu____8907 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____8924  ->
                                                  let uu____8925 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____8926 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____8925 uu____8926);
                                             (let uu____8927 =
                                                let uu____8930 =
                                                  let uu____8931 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8931 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____8930 opts label1
                                                 in
                                              bind uu____8927
                                                (fun uu____8938  ->
                                                   let uu____8939 =
                                                     bind rewriter
                                                       (fun uu____8953  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____8959 
                                                               ->
                                                               let uu____8960
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____8961
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____8960
                                                                 uu____8961);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____8939)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____9002 =
        bind get
          (fun ps  ->
             let uu____9012 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9012 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9049  ->
                       let uu____9050 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____9050);
                  bind dismiss_all
                    (fun uu____9053  ->
                       let uu____9054 =
                         let uu____9061 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9061
                           keepGoing gt1
                          in
                       bind uu____9054
                         (fun uu____9073  ->
                            match uu____9073 with
                            | (gt',uu____9081) ->
                                (log ps
                                   (fun uu____9085  ->
                                      let uu____9086 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____9086);
                                 (let uu____9087 = push_goals gs  in
                                  bind uu____9087
                                    (fun uu____9092  ->
                                       let uu____9093 =
                                         let uu____9096 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____9096]  in
                                       add_goals uu____9093)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____9002
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____9119 =
        bind get
          (fun ps  ->
             let uu____9129 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9129 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9166  ->
                       let uu____9167 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____9167);
                  bind dismiss_all
                    (fun uu____9170  ->
                       let uu____9171 =
                         let uu____9174 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9174 gt1
                          in
                       bind uu____9171
                         (fun gt'  ->
                            log ps
                              (fun uu____9182  ->
                                 let uu____9183 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____9183);
                            (let uu____9184 = push_goals gs  in
                             bind uu____9184
                               (fun uu____9189  ->
                                  let uu____9190 =
                                    let uu____9193 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____9193]  in
                                  add_goals uu____9190))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____9119
  
let (trefl : unit -> unit tac) =
  fun uu____9204  ->
    let uu____9207 =
      let uu____9210 = cur_goal ()  in
      bind uu____9210
        (fun g  ->
           let uu____9228 =
             let uu____9233 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____9233  in
           match uu____9228 with
           | FStar_Pervasives_Native.Some t ->
               let uu____9241 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____9241 with
                | (hd1,args) ->
                    let uu____9280 =
                      let uu____9293 =
                        let uu____9294 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9294.FStar_Syntax_Syntax.n  in
                      (uu____9293, args)  in
                    (match uu____9280 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9308::(l,uu____9310)::(r,uu____9312)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9359 =
                           let uu____9362 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9362 l r  in
                         bind uu____9359
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9369 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9369 l
                                    in
                                 let r1 =
                                   let uu____9371 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9371 r
                                    in
                                 let uu____9372 =
                                   let uu____9375 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9375 l1 r1  in
                                 bind uu____9372
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9381 =
                                           let uu____9382 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9382 l1  in
                                         let uu____9383 =
                                           let uu____9384 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9384 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9381 uu____9383))))
                     | (hd2,uu____9386) ->
                         let uu____9403 =
                           let uu____9404 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9404 t  in
                         fail1 "trefl: not an equality (%s)" uu____9403))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____9207
  
let (dup : unit -> unit tac) =
  fun uu____9417  ->
    let uu____9420 = cur_goal ()  in
    bind uu____9420
      (fun g  ->
         let uu____9426 =
           let uu____9433 = FStar_Tactics_Types.goal_env g  in
           let uu____9434 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9433 uu____9434  in
         bind uu____9426
           (fun uu____9443  ->
              match uu____9443 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___420_9453 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___420_9453.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___420_9453.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___420_9453.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___420_9453.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____9456  ->
                       let uu____9457 =
                         let uu____9460 = FStar_Tactics_Types.goal_env g  in
                         let uu____9461 =
                           let uu____9462 =
                             let uu____9463 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9464 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9463
                               uu____9464
                              in
                           let uu____9465 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9466 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9462 uu____9465 u
                             uu____9466
                            in
                         add_irrelevant_goal "dup equation" uu____9460
                           uu____9461 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____9457
                         (fun uu____9469  ->
                            let uu____9470 = add_goals [g']  in
                            bind uu____9470 (fun uu____9474  -> ret ())))))
  
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
              let uu____9597 = f x y  in
              if uu____9597 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9617 -> (acc, l11, l21)  in
        let uu____9632 = aux [] l1 l2  in
        match uu____9632 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9737 = get_phi g1  in
      match uu____9737 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9743 = get_phi g2  in
          (match uu____9743 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9755 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9755 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9786 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____9786 phi1  in
                    let t2 =
                      let uu____9796 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____9796 phi2  in
                    let uu____9805 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9805
                      (fun uu____9810  ->
                         let uu____9811 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9811
                           (fun uu____9818  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___421_9823 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9824 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___421_9823.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___421_9823.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___421_9823.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___421_9823.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9824;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___421_9823.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___421_9823.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___421_9823.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___421_9823.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___421_9823.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___421_9823.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___421_9823.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___421_9823.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___421_9823.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___421_9823.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___421_9823.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___421_9823.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___421_9823.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___421_9823.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___421_9823.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___421_9823.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___421_9823.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___421_9823.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___421_9823.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___421_9823.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___421_9823.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___421_9823.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___421_9823.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___421_9823.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___421_9823.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___421_9823.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___421_9823.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___421_9823.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___421_9823.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___421_9823.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___421_9823.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___421_9823.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___421_9823.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___421_9823.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___421_9823.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___421_9823.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___421_9823.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9827 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____9827
                                (fun goal  ->
                                   mlog
                                     (fun uu____9836  ->
                                        let uu____9837 =
                                          goal_to_string_verbose g1  in
                                        let uu____9838 =
                                          goal_to_string_verbose g2  in
                                        let uu____9839 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9837 uu____9838 uu____9839)
                                     (fun uu____9841  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9848  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9864 =
               set
                 (let uu___422_9869 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___422_9869.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___422_9869.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___422_9869.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___422_9869.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___422_9869.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___422_9869.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___422_9869.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___422_9869.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___422_9869.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___422_9869.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___422_9869.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___422_9869.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9864
               (fun uu____9872  ->
                  let uu____9873 = join_goals g1 g2  in
                  bind uu____9873 (fun g12  -> add_goals [g12]))
         | uu____9878 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9898 =
      let uu____9905 = cur_goal ()  in
      bind uu____9905
        (fun g  ->
           let uu____9915 =
             let uu____9924 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9924 t  in
           bind uu____9915
             (fun uu____9952  ->
                match uu____9952 with
                | (t1,typ,guard) ->
                    let uu____9968 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9968 with
                     | (hd1,args) ->
                         let uu____10017 =
                           let uu____10032 =
                             let uu____10033 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____10033.FStar_Syntax_Syntax.n  in
                           (uu____10032, args)  in
                         (match uu____10017 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____10054)::(q,uu____10056)::[]) when
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
                                let uu____10110 =
                                  let uu____10111 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____10111
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____10110
                                 in
                              let g2 =
                                let uu____10113 =
                                  let uu____10114 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____10114
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____10113
                                 in
                              bind __dismiss
                                (fun uu____10121  ->
                                   let uu____10122 = add_goals [g1; g2]  in
                                   bind uu____10122
                                     (fun uu____10131  ->
                                        let uu____10132 =
                                          let uu____10137 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____10138 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____10137, uu____10138)  in
                                        ret uu____10132))
                          | uu____10143 ->
                              let uu____10158 =
                                let uu____10159 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____10159 typ  in
                              fail1 "Not a disjunction: %s" uu____10158))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9898
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____10189 =
      let uu____10192 = cur_goal ()  in
      bind uu____10192
        (fun g  ->
           FStar_Options.push ();
           (let uu____10205 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____10205);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___423_10212 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___423_10212.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___423_10212.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___423_10212.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___423_10212.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____10189
  
let (top_env : unit -> env tac) =
  fun uu____10224  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10237  ->
    let uu____10240 = cur_goal ()  in
    bind uu____10240
      (fun g  ->
         let uu____10246 =
           (FStar_Options.lax ()) ||
             (let uu____10248 = FStar_Tactics_Types.goal_env g  in
              uu____10248.FStar_TypeChecker_Env.lax)
            in
         ret uu____10246)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10263 =
        mlog
          (fun uu____10268  ->
             let uu____10269 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10269)
          (fun uu____10272  ->
             let uu____10273 = cur_goal ()  in
             bind uu____10273
               (fun goal  ->
                  let env =
                    let uu____10281 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10281 ty  in
                  let uu____10282 = __tc_ghost env tm  in
                  bind uu____10282
                    (fun uu____10301  ->
                       match uu____10301 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10315  ->
                                let uu____10316 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10316)
                             (fun uu____10318  ->
                                mlog
                                  (fun uu____10321  ->
                                     let uu____10322 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10322)
                                  (fun uu____10325  ->
                                     let uu____10326 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10326
                                       (fun uu____10330  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10263
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10353 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10359 =
              let uu____10366 =
                let uu____10367 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10367
                 in
              new_uvar "uvar_env.2" env uu____10366  in
            bind uu____10359
              (fun uu____10383  ->
                 match uu____10383 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10353
        (fun typ  ->
           let uu____10395 = new_uvar "uvar_env" env typ  in
           bind uu____10395
             (fun uu____10409  ->
                match uu____10409 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10427 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10446 -> g.FStar_Tactics_Types.opts
             | uu____10449 -> FStar_Options.peek ()  in
           let uu____10452 = FStar_Syntax_Util.head_and_args t  in
           match uu____10452 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10472);
                FStar_Syntax_Syntax.pos = uu____10473;
                FStar_Syntax_Syntax.vars = uu____10474;_},uu____10475)
               ->
               let env1 =
                 let uu___424_10517 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___424_10517.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___424_10517.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___424_10517.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___424_10517.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___424_10517.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___424_10517.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___424_10517.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___424_10517.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___424_10517.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___424_10517.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___424_10517.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___424_10517.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___424_10517.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___424_10517.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___424_10517.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___424_10517.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___424_10517.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___424_10517.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___424_10517.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___424_10517.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___424_10517.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___424_10517.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___424_10517.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___424_10517.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___424_10517.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___424_10517.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___424_10517.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___424_10517.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___424_10517.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___424_10517.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___424_10517.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___424_10517.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___424_10517.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___424_10517.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___424_10517.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___424_10517.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___424_10517.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___424_10517.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___424_10517.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___424_10517.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___424_10517.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___424_10517.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____10519 =
                 let uu____10522 = bnorm_goal g  in [uu____10522]  in
               add_goals uu____10519
           | uu____10523 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10427
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10572 = if b then t2 else ret false  in
             bind uu____10572 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10583 = trytac comp  in
      bind uu____10583
        (fun uu___354_10591  ->
           match uu___354_10591 with
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
        let uu____10617 =
          bind get
            (fun ps  ->
               let uu____10623 = __tc e t1  in
               bind uu____10623
                 (fun uu____10643  ->
                    match uu____10643 with
                    | (t11,ty1,g1) ->
                        let uu____10655 = __tc e t2  in
                        bind uu____10655
                          (fun uu____10675  ->
                             match uu____10675 with
                             | (t21,ty2,g2) ->
                                 let uu____10687 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10687
                                   (fun uu____10692  ->
                                      let uu____10693 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10693
                                        (fun uu____10699  ->
                                           let uu____10700 =
                                             do_unify e ty1 ty2  in
                                           let uu____10703 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10700 uu____10703)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10617
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10736  ->
             let uu____10737 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10737
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
        (fun uu____10758  ->
           let uu____10759 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10759)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10769 =
      mlog
        (fun uu____10774  ->
           let uu____10775 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10775)
        (fun uu____10778  ->
           let uu____10779 = cur_goal ()  in
           bind uu____10779
             (fun g  ->
                let uu____10785 =
                  let uu____10794 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10794 ty  in
                bind uu____10785
                  (fun uu____10806  ->
                     match uu____10806 with
                     | (ty1,uu____10816,guard) ->
                         let uu____10818 =
                           let uu____10821 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10821 guard  in
                         bind uu____10818
                           (fun uu____10824  ->
                              let uu____10825 =
                                let uu____10828 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10829 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10828 uu____10829 ty1  in
                              bind uu____10825
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10835 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10835
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10841 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10842 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10841
                                          uu____10842
                                         in
                                      let nty =
                                        let uu____10844 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10844 ty1  in
                                      let uu____10845 =
                                        let uu____10848 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10848 ng nty  in
                                      bind uu____10845
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10854 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10854
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10769
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10917 =
      let uu____10926 = cur_goal ()  in
      bind uu____10926
        (fun g  ->
           let uu____10938 =
             let uu____10947 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10947 s_tm  in
           bind uu____10938
             (fun uu____10965  ->
                match uu____10965 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10983 =
                      let uu____10986 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10986 guard  in
                    bind uu____10983
                      (fun uu____10998  ->
                         let uu____10999 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10999 with
                         | (h,args) ->
                             let uu____11044 =
                               let uu____11051 =
                                 let uu____11052 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____11052.FStar_Syntax_Syntax.n  in
                               match uu____11051 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____11067;
                                      FStar_Syntax_Syntax.vars = uu____11068;_},us)
                                   -> ret (fv, us)
                               | uu____11078 -> fail "type is not an fv"  in
                             bind uu____11044
                               (fun uu____11098  ->
                                  match uu____11098 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____11114 =
                                        let uu____11117 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____11117 t_lid
                                         in
                                      (match uu____11114 with
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
                                                  (fun uu____11166  ->
                                                     let uu____11167 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____11167 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____11182 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____11210
                                                                  =
                                                                  let uu____11213
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____11213
                                                                    c_lid
                                                                   in
                                                                match uu____11210
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
                                                                    uu____11283
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
                                                                    let uu____11288
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11288
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11311
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11311
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11354
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11354
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11427
                                                                    =
                                                                    let uu____11428
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11428
                                                                     in
                                                                    failwhen
                                                                    uu____11427
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11445
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
                                                                    uu___355_11461
                                                                    =
                                                                    match uu___355_11461
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11464)
                                                                    -> true
                                                                    | 
                                                                    uu____11465
                                                                    -> false
                                                                     in
                                                                    let uu____11468
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11468
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
                                                                    uu____11601
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
                                                                    uu____11663
                                                                     ->
                                                                    match uu____11663
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11683),
                                                                    (t,uu____11685))
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
                                                                    uu____11753
                                                                     ->
                                                                    match uu____11753
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11779),
                                                                    (t,uu____11781))
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
                                                                    uu____11836
                                                                     ->
                                                                    match uu____11836
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
                                                                    let uu____11886
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___425_11903
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___425_11903.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____11886
                                                                    with
                                                                    | 
                                                                    (uu____11916,uu____11917,uu____11918,pat_t,uu____11920,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11927
                                                                    =
                                                                    let uu____11928
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11928
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11927
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11932
                                                                    =
                                                                    let uu____11941
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11941]
                                                                     in
                                                                    let uu____11960
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11932
                                                                    uu____11960
                                                                     in
                                                                    let nty =
                                                                    let uu____11966
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11966
                                                                     in
                                                                    let uu____11969
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11969
                                                                    (fun
                                                                    uu____11998
                                                                     ->
                                                                    match uu____11998
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
                                                                    let uu____12024
                                                                    =
                                                                    let uu____12035
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____12035]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____12024
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____12071
                                                                    =
                                                                    let uu____12082
                                                                    =
                                                                    let uu____12087
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____12087)
                                                                     in
                                                                    (g', br,
                                                                    uu____12082)
                                                                     in
                                                                    ret
                                                                    uu____12071))))))
                                                                    | 
                                                                    uu____12108
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____11182
                                                           (fun goal_brs  ->
                                                              let uu____12157
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____12157
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
                                                                  let uu____12230
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12230
                                                                    (
                                                                    fun
                                                                    uu____12241
                                                                     ->
                                                                    let uu____12242
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12242
                                                                    (fun
                                                                    uu____12252
                                                                     ->
                                                                    ret infos))))
                                            | uu____12259 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10917
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12304::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12332 = init xs  in x :: uu____12332
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12344 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12353) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12418 = last args  in
          (match uu____12418 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12448 =
                 let uu____12449 =
                   let uu____12454 =
                     let uu____12455 =
                       let uu____12460 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12460  in
                     uu____12455 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12454, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12449  in
               FStar_All.pipe_left ret uu____12448)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12473,uu____12474) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12526 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12526 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12567 =
                      let uu____12568 =
                        let uu____12573 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12573)  in
                      FStar_Reflection_Data.Tv_Abs uu____12568  in
                    FStar_All.pipe_left ret uu____12567))
      | FStar_Syntax_Syntax.Tm_type uu____12576 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12600 ->
          let uu____12615 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12615 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12645 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12645 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12698 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12710 =
            let uu____12711 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12711  in
          FStar_All.pipe_left ret uu____12710
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12732 =
            let uu____12733 =
              let uu____12738 =
                let uu____12739 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12739  in
              (uu____12738, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12733  in
          FStar_All.pipe_left ret uu____12732
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12773 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12778 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12778 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12831 ->
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
             | FStar_Util.Inr uu____12865 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12869 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12869 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12889 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12893 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12947 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12947
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12966 =
                  let uu____12973 =
                    FStar_List.map
                      (fun uu____12985  ->
                         match uu____12985 with
                         | (p1,uu____12993) -> inspect_pat p1) ps
                     in
                  (fv, uu____12973)  in
                FStar_Reflection_Data.Pat_Cons uu____12966
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
              (fun uu___356_13087  ->
                 match uu___356_13087 with
                 | (pat,uu____13109,t5) ->
                     let uu____13127 = inspect_pat pat  in (uu____13127, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____13136 ->
          ((let uu____13138 =
              let uu____13143 =
                let uu____13144 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____13145 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____13144 uu____13145
                 in
              (FStar_Errors.Warning_CantInspect, uu____13143)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____13138);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12344
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____13158 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____13158
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____13162 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____13162
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____13166 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____13166
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____13173 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____13173
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____13198 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____13198
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____13215 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____13215
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13234 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13234
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13238 =
          let uu____13239 =
            let uu____13246 =
              let uu____13247 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13247  in
            FStar_Syntax_Syntax.mk uu____13246  in
          uu____13239 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13238
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13255 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13255
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13264 =
          let uu____13265 =
            let uu____13272 =
              let uu____13273 =
                let uu____13286 =
                  let uu____13289 =
                    let uu____13290 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13290]  in
                  FStar_Syntax_Subst.close uu____13289 t2  in
                ((false, [lb]), uu____13286)  in
              FStar_Syntax_Syntax.Tm_let uu____13273  in
            FStar_Syntax_Syntax.mk uu____13272  in
          uu____13265 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13264
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13330 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13330 with
         | (lbs,body) ->
             let uu____13345 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13345)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13379 =
                let uu____13380 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13380  in
              FStar_All.pipe_left wrap uu____13379
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13387 =
                let uu____13388 =
                  let uu____13401 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13417 = pack_pat p1  in
                         (uu____13417, false)) ps
                     in
                  (fv, uu____13401)  in
                FStar_Syntax_Syntax.Pat_cons uu____13388  in
              FStar_All.pipe_left wrap uu____13387
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
            (fun uu___357_13463  ->
               match uu___357_13463 with
               | (pat,t1) ->
                   let uu____13480 = pack_pat pat  in
                   (uu____13480, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13528 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13528
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13556 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13556
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13602 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13602
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13641 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13641
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13658 =
        bind get
          (fun ps  ->
             let uu____13664 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13664 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13658
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13693 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___426_13700 = ps  in
                 let uu____13701 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___426_13700.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___426_13700.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___426_13700.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___426_13700.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___426_13700.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___426_13700.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___426_13700.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___426_13700.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___426_13700.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___426_13700.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___426_13700.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___426_13700.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13701
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13693
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13726 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13726 with
      | (u,ctx_uvars,g_u) ->
          let uu____13758 = FStar_List.hd ctx_uvars  in
          (match uu____13758 with
           | (ctx_uvar,uu____13772) ->
               let g =
                 let uu____13774 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13774 false
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
        let uu____13794 = goal_of_goal_ty env typ  in
        match uu____13794 with
        | (g,g_u) ->
            let ps =
              let uu____13806 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13807 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13806;
                FStar_Tactics_Types.local_state = uu____13807
              }  in
            let uu____13814 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13814)
  