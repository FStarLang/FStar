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
        (try (fun uu___359_158  -> match () with | () -> run t p) ()
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
    FStar_Util.format2 "%s%s\n" uu____295 uu____296
  
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
            let uu____335 = FStar_Options.print_implicits ()  in
            if uu____335
            then
              let uu____336 = FStar_Tactics_Types.goal_env g  in
              let uu____337 = FStar_Tactics_Types.goal_witness g  in
              tts uu____336 uu____337
            else
              (let uu____339 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____339 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____343 = FStar_Tactics_Types.goal_env g  in
                   let uu____344 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____343 uu____344)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____356 = FStar_Util.string_of_int i  in
                let uu____357 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____356 uu____357
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.strcat " (" (Prims.strcat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____362 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____363 =
                 let uu____364 = FStar_Tactics_Types.goal_env g  in
                 tts uu____364
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____362 w uu____363)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____380 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____380
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____396 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____396
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____417 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____417
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____424) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____434) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____453 =
      let uu____454 = FStar_Tactics_Types.goal_env g  in
      let uu____455 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____454 uu____455  in
    FStar_Syntax_Util.un_squash uu____453
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____461 = get_phi g  in FStar_Option.isSome uu____461 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____480  ->
    bind get
      (fun ps  ->
         let uu____486 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____486)
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____495  ->
    match uu____495 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____521 =
          let uu____524 =
            let uu____527 =
              let uu____528 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____528
                msg
               in
            let uu____529 =
              let uu____532 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____533 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____533
                else ""  in
              let uu____535 =
                let uu____538 =
                  let uu____539 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____539
                  then
                    let uu____540 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____540
                  else ""  in
                [uu____538]  in
              uu____532 :: uu____535  in
            uu____527 :: uu____529  in
          let uu____542 =
            let uu____545 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____556 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____545 uu____556  in
          FStar_List.append uu____524 uu____542  in
        FStar_String.concat "" uu____521
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____577 =
        let uu____578 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____578  in
      let uu____579 =
        let uu____584 =
          let uu____585 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____585  in
        FStar_Syntax_Print.binders_to_json uu____584  in
      FStar_All.pipe_right uu____577 uu____579  in
    let uu____586 =
      let uu____593 =
        let uu____600 =
          let uu____605 =
            let uu____606 =
              let uu____613 =
                let uu____618 =
                  let uu____619 =
                    let uu____620 = FStar_Tactics_Types.goal_env g  in
                    let uu____621 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____620 uu____621  in
                  FStar_Util.JsonStr uu____619  in
                ("witness", uu____618)  in
              let uu____622 =
                let uu____629 =
                  let uu____634 =
                    let uu____635 =
                      let uu____636 = FStar_Tactics_Types.goal_env g  in
                      let uu____637 = FStar_Tactics_Types.goal_type g  in
                      tts uu____636 uu____637  in
                    FStar_Util.JsonStr uu____635  in
                  ("type", uu____634)  in
                [uu____629;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____613 :: uu____622  in
            FStar_Util.JsonAssoc uu____606  in
          ("goal", uu____605)  in
        [uu____600]  in
      ("hyps", g_binders) :: uu____593  in
    FStar_Util.JsonAssoc uu____586
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____674  ->
    match uu____674 with
    | (msg,ps) ->
        let uu____681 =
          let uu____688 =
            let uu____695 =
              let uu____702 =
                let uu____709 =
                  let uu____714 =
                    let uu____715 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____715  in
                  ("goals", uu____714)  in
                let uu____718 =
                  let uu____725 =
                    let uu____730 =
                      let uu____731 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____731  in
                    ("smt-goals", uu____730)  in
                  [uu____725]  in
                uu____709 :: uu____718  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____702
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____695  in
          let uu____754 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____767 =
                let uu____772 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____772)  in
              [uu____767]
            else []  in
          FStar_List.append uu____688 uu____754  in
        FStar_Util.JsonAssoc uu____681
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____802  ->
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
         (let uu____825 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____825 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
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
         FStar_Tactics_Result.Failed (msg, ps))
  
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
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
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
  
let recover : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
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
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1289  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___363_1303 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_1303.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_1303.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___363_1303.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___363_1303.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_1303.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_1303.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_1303.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_1303.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___363_1303.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___363_1303.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_1303.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___363_1303.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1324 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1324
         then
           let uu____1325 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1326 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1325
             uu____1326
         else ());
        (try
           (fun uu___365_1333  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1340 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1340
                    then
                      let uu____1341 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1342 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1343 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1341
                        uu____1342 uu____1343
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1348 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1348 (fun uu____1352  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1359,msg) ->
             mlog
               (fun uu____1362  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1364  -> ret false)
         | FStar_Errors.Error (uu____1365,msg,r) ->
             mlog
               (fun uu____1370  ->
                  let uu____1371 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1371) (fun uu____1373  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___366_1384 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___366_1384.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___366_1384.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___366_1384.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___367_1387 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___367_1387.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___367_1387.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___367_1387.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___367_1387.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___367_1387.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___367_1387.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___367_1387.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___367_1387.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___367_1387.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___367_1387.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___367_1387.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___367_1387.FStar_Tactics_Types.local_state)
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
          (fun uu____1410  ->
             (let uu____1412 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1412
              then
                (FStar_Options.push ();
                 (let uu____1414 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1416 = __do_unify env t1 t2  in
              bind uu____1416
                (fun r  ->
                   (let uu____1423 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1423 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1426  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___368_1433 = ps  in
         let uu____1434 =
           FStar_List.filter
             (fun g  ->
                let uu____1440 = check_goal_solved g  in
                FStar_Option.isNone uu____1440) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___368_1433.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___368_1433.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___368_1433.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1434;
           FStar_Tactics_Types.smt_goals =
             (uu___368_1433.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___368_1433.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___368_1433.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___368_1433.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___368_1433.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___368_1433.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___368_1433.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___368_1433.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___368_1433.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1457 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1457 with
      | FStar_Pervasives_Native.Some uu____1462 ->
          let uu____1463 =
            let uu____1464 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1464  in
          fail uu____1463
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1480 = FStar_Tactics_Types.goal_env goal  in
      let uu____1481 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1480 solution uu____1481
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1487 =
         let uu___369_1488 = p  in
         let uu____1489 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___369_1488.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___369_1488.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___369_1488.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1489;
           FStar_Tactics_Types.smt_goals =
             (uu___369_1488.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___369_1488.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___369_1488.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___369_1488.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___369_1488.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___369_1488.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___369_1488.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___369_1488.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___369_1488.FStar_Tactics_Types.local_state)
         }  in
       set uu____1487)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1510  ->
           let uu____1511 =
             let uu____1512 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1512  in
           let uu____1513 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1511 uu____1513)
        (fun uu____1516  ->
           let uu____1517 = trysolve goal solution  in
           bind uu____1517
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1525  -> remove_solved_goals)
                else
                  (let uu____1527 =
                     let uu____1528 =
                       let uu____1529 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1529 solution  in
                     let uu____1530 =
                       let uu____1531 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1532 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1531 uu____1532  in
                     let uu____1533 =
                       let uu____1534 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1535 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1534 uu____1535  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1528 uu____1530 uu____1533
                      in
                   fail uu____1527)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1550 = set_solution goal solution  in
      bind uu____1550
        (fun uu____1554  ->
           bind __dismiss (fun uu____1556  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___370_1574 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1574.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1574.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1574.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___370_1574.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1574.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1574.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1574.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1574.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1574.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1574.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1574.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1574.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___371_1592 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1592.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1592.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___371_1592.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1592.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___371_1592.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1592.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1592.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1592.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1592.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1592.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1592.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1592.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1613 = FStar_Options.defensive ()  in
    if uu____1613
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1618 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1618)
         in
      let b2 =
        b1 &&
          (let uu____1621 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1621)
         in
      let rec aux b3 e =
        let uu____1633 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1633 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1651 =
        (let uu____1654 = aux b2 env  in Prims.op_Negation uu____1654) &&
          (let uu____1656 = FStar_ST.op_Bang nwarn  in
           uu____1656 < (Prims.parse_int "5"))
         in
      (if uu____1651
       then
         ((let uu____1677 =
             let uu____1678 = FStar_Tactics_Types.goal_type g  in
             uu____1678.FStar_Syntax_Syntax.pos  in
           let uu____1681 =
             let uu____1686 =
               let uu____1687 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1687
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1686)  in
           FStar_Errors.log_issue uu____1677 uu____1681);
          (let uu____1688 =
             let uu____1689 = FStar_ST.op_Bang nwarn  in
             uu____1689 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1688))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___372_1749 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1749.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1749.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_1749.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___372_1749.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_1749.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1749.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1749.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1749.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_1749.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_1749.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_1749.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_1749.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___373_1769 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___373_1769.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___373_1769.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___373_1769.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___373_1769.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___373_1769.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___373_1769.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___373_1769.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___373_1769.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___373_1769.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___373_1769.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___373_1769.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___373_1769.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___374_1789 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___374_1789.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___374_1789.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___374_1789.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___374_1789.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___374_1789.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___374_1789.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___374_1789.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___374_1789.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___374_1789.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___374_1789.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___374_1789.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___374_1789.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___375_1809 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___375_1809.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___375_1809.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___375_1809.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___375_1809.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___375_1809.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___375_1809.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___375_1809.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___375_1809.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___375_1809.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___375_1809.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___375_1809.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___375_1809.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1820  -> add_goals [g]) 
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
        let uu____1848 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1848 with
        | (u,ctx_uvar,g_u) ->
            let uu____1882 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1882
              (fun uu____1891  ->
                 let uu____1892 =
                   let uu____1897 =
                     let uu____1898 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1898  in
                   (u, uu____1897)  in
                 ret uu____1892)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1916 = FStar_Syntax_Util.un_squash t  in
    match uu____1916 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1926 =
          let uu____1927 = FStar_Syntax_Subst.compress t'  in
          uu____1927.FStar_Syntax_Syntax.n  in
        (match uu____1926 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1931 -> false)
    | uu____1932 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1942 = FStar_Syntax_Util.un_squash t  in
    match uu____1942 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1952 =
          let uu____1953 = FStar_Syntax_Subst.compress t'  in
          uu____1953.FStar_Syntax_Syntax.n  in
        (match uu____1952 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1957 -> false)
    | uu____1958 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1969  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1980 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1980 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1987 = goal_to_string_verbose hd1  in
                    let uu____1988 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1987 uu____1988);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____1998 =
      bind get
        (fun ps  ->
           let uu____2004 = cur_goal ()  in
           bind uu____2004
             (fun g  ->
                (let uu____2011 =
                   let uu____2012 = FStar_Tactics_Types.goal_type g  in
                   uu____2012.FStar_Syntax_Syntax.pos  in
                 let uu____2015 =
                   let uu____2020 =
                     let uu____2021 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2021
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2020)  in
                 FStar_Errors.log_issue uu____2011 uu____2015);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____1998
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2036  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___376_2046 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___376_2046.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___376_2046.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___376_2046.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___376_2046.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___376_2046.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___376_2046.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___376_2046.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___376_2046.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___376_2046.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___376_2046.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___376_2046.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___376_2046.FStar_Tactics_Types.local_state)
           }  in
         let uu____2047 = set ps1  in
         bind uu____2047
           (fun uu____2052  ->
              let uu____2053 = FStar_BigInt.of_int_fs n1  in ret uu____2053))
  
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
              let uu____2086 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2086 phi  in
            let uu____2087 = new_uvar reason env typ  in
            bind uu____2087
              (fun uu____2102  ->
                 match uu____2102 with
                 | (uu____2109,ctx_uvar) ->
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
             (fun uu____2154  ->
                let uu____2155 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2155)
             (fun uu____2158  ->
                let e1 =
                  let uu___377_2160 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___377_2160.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___377_2160.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___377_2160.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___377_2160.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___377_2160.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___377_2160.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___377_2160.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___377_2160.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___377_2160.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___377_2160.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___377_2160.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___377_2160.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___377_2160.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___377_2160.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___377_2160.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___377_2160.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___377_2160.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___377_2160.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___377_2160.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___377_2160.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___377_2160.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___377_2160.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___377_2160.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___377_2160.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___377_2160.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___377_2160.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___377_2160.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___377_2160.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___377_2160.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___377_2160.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___377_2160.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___377_2160.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___377_2160.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___377_2160.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___377_2160.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___377_2160.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___377_2160.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___377_2160.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___377_2160.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___377_2160.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___377_2160.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___377_2160.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___379_2171  ->
                     match () with
                     | () ->
                         let uu____2180 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2180) ()
                with
                | FStar_Errors.Err (uu____2207,msg) ->
                    let uu____2209 = tts e1 t  in
                    let uu____2210 =
                      let uu____2211 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2211
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2209 uu____2210 msg
                | FStar_Errors.Error (uu____2218,msg,uu____2220) ->
                    let uu____2221 = tts e1 t  in
                    let uu____2222 =
                      let uu____2223 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2223
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2221 uu____2222 msg))
  
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
             (fun uu____2272  ->
                let uu____2273 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2273)
             (fun uu____2276  ->
                let e1 =
                  let uu___380_2278 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___380_2278.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___380_2278.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___380_2278.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___380_2278.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___380_2278.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___380_2278.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___380_2278.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___380_2278.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___380_2278.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___380_2278.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___380_2278.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___380_2278.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___380_2278.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___380_2278.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___380_2278.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___380_2278.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___380_2278.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___380_2278.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___380_2278.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___380_2278.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___380_2278.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___380_2278.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___380_2278.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___380_2278.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___380_2278.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___380_2278.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___380_2278.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___380_2278.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___380_2278.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___380_2278.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___380_2278.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___380_2278.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___380_2278.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___380_2278.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___380_2278.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___380_2278.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___380_2278.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___380_2278.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___380_2278.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___380_2278.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___380_2278.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___380_2278.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___382_2292  ->
                     match () with
                     | () ->
                         let uu____2301 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2301 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2339,msg) ->
                    let uu____2341 = tts e1 t  in
                    let uu____2342 =
                      let uu____2343 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2343
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2341 uu____2342 msg
                | FStar_Errors.Error (uu____2350,msg,uu____2352) ->
                    let uu____2353 = tts e1 t  in
                    let uu____2354 =
                      let uu____2355 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2355
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2353 uu____2354 msg))
  
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
             (fun uu____2404  ->
                let uu____2405 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2405)
             (fun uu____2409  ->
                let e1 =
                  let uu___383_2411 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___383_2411.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___383_2411.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___383_2411.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___383_2411.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___383_2411.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___383_2411.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___383_2411.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___383_2411.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___383_2411.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___383_2411.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___383_2411.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___383_2411.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___383_2411.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___383_2411.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___383_2411.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___383_2411.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___383_2411.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___383_2411.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___383_2411.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___383_2411.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___383_2411.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___383_2411.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___383_2411.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___383_2411.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___383_2411.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___383_2411.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___383_2411.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___383_2411.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___383_2411.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___383_2411.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___383_2411.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___383_2411.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___383_2411.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___383_2411.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___383_2411.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___383_2411.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___383_2411.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___383_2411.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___383_2411.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___383_2411.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___383_2411.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___383_2411.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___384_2413 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___384_2413.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___384_2413.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___384_2413.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___384_2413.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___384_2413.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___384_2413.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___384_2413.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___384_2413.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___384_2413.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___384_2413.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___384_2413.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___384_2413.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___384_2413.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___384_2413.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___384_2413.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___384_2413.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___384_2413.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___384_2413.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___384_2413.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___384_2413.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___384_2413.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___384_2413.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___384_2413.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___384_2413.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___384_2413.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___384_2413.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___384_2413.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___384_2413.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___384_2413.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___384_2413.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___384_2413.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___384_2413.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___384_2413.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___384_2413.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___384_2413.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___384_2413.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___384_2413.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___384_2413.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___384_2413.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___384_2413.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___384_2413.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___384_2413.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___386_2427  ->
                     match () with
                     | () ->
                         let uu____2436 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2436 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2474,msg) ->
                    let uu____2476 = tts e2 t  in
                    let uu____2477 =
                      let uu____2478 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2478
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2476 uu____2477 msg
                | FStar_Errors.Error (uu____2485,msg,uu____2487) ->
                    let uu____2488 = tts e2 t  in
                    let uu____2489 =
                      let uu____2490 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____2490
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2488 uu____2489 msg))
  
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
  fun uu____2517  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___387_2535 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___387_2535.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___387_2535.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___387_2535.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___387_2535.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___387_2535.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___387_2535.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___387_2535.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___387_2535.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___387_2535.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___387_2535.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___387_2535.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___387_2535.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2559 = get_guard_policy ()  in
      bind uu____2559
        (fun old_pol  ->
           let uu____2565 = set_guard_policy pol  in
           bind uu____2565
             (fun uu____2569  ->
                bind t
                  (fun r  ->
                     let uu____2573 = set_guard_policy old_pol  in
                     bind uu____2573 (fun uu____2577  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2580 = let uu____2585 = cur_goal ()  in trytac uu____2585  in
  bind uu____2580
    (fun uu___350_2592  ->
       match uu___350_2592 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2598 = FStar_Options.peek ()  in ret uu____2598)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2620  ->
             let uu____2621 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2621)
          (fun uu____2624  ->
             let uu____2625 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2625
               (fun uu____2629  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2633 =
                         let uu____2634 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2634.FStar_TypeChecker_Env.guard_f  in
                       match uu____2633 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2638 = istrivial e f  in
                           if uu____2638
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2648 =
                                          let uu____2653 =
                                            let uu____2654 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2654
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2653)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2648);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2657  ->
                                           let uu____2658 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2658)
                                        (fun uu____2661  ->
                                           let uu____2662 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2662
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___388_2669 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___388_2669.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___388_2669.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___388_2669.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___388_2669.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2672  ->
                                           let uu____2673 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2673)
                                        (fun uu____2676  ->
                                           let uu____2677 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____2677
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___389_2684 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___389_2684.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___389_2684.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___389_2684.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___389_2684.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2687  ->
                                           let uu____2688 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2688)
                                        (fun uu____2690  ->
                                           try
                                             (fun uu___391_2695  ->
                                                match () with
                                                | () ->
                                                    let uu____2698 =
                                                      let uu____2699 =
                                                        let uu____2700 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2700
                                                         in
                                                      Prims.op_Negation
                                                        uu____2699
                                                       in
                                                    if uu____2698
                                                    then
                                                      mlog
                                                        (fun uu____2705  ->
                                                           let uu____2706 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2706)
                                                        (fun uu____2708  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___390_2711 ->
                                               mlog
                                                 (fun uu____2716  ->
                                                    let uu____2717 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2717)
                                                 (fun uu____2719  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2729 =
      let uu____2732 = cur_goal ()  in
      bind uu____2732
        (fun goal  ->
           let uu____2738 =
             let uu____2747 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____2747 t  in
           bind uu____2738
             (fun uu____2758  ->
                match uu____2758 with
                | (uu____2767,typ,uu____2769) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2729
  
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
            let uu____2803 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____2803 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2814  ->
    let uu____2817 = cur_goal ()  in
    bind uu____2817
      (fun goal  ->
         let uu____2823 =
           let uu____2824 = FStar_Tactics_Types.goal_env goal  in
           let uu____2825 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2824 uu____2825  in
         if uu____2823
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2829 =
              let uu____2830 = FStar_Tactics_Types.goal_env goal  in
              let uu____2831 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2830 uu____2831  in
            fail1 "Not a trivial goal: %s" uu____2829))
  
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
             let uu____2880 =
               try
                 (fun uu___396_2903  ->
                    match () with
                    | () ->
                        let uu____2914 =
                          let uu____2923 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2923
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2914) ()
               with | uu___395_2933 -> fail "divide: not enough goals"  in
             bind uu____2880
               (fun uu____2969  ->
                  match uu____2969 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___392_2995 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___392_2995.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___392_2995.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___392_2995.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___392_2995.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___392_2995.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___392_2995.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___392_2995.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___392_2995.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___392_2995.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___392_2995.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___392_2995.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2996 = set lp  in
                      bind uu____2996
                        (fun uu____3004  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___393_3020 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___393_3020.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___393_3020.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___393_3020.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___393_3020.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___393_3020.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___393_3020.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___393_3020.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___393_3020.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___393_3020.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___393_3020.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___393_3020.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3021 = set rp  in
                                     bind uu____3021
                                       (fun uu____3029  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___394_3045 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___394_3045.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___394_3045.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3046 = set p'
                                                       in
                                                    bind uu____3046
                                                      (fun uu____3054  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3060 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3081 = divide FStar_BigInt.one f idtac  in
    bind uu____3081
      (fun uu____3094  -> match uu____3094 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3131::uu____3132 ->
             let uu____3135 =
               let uu____3144 = map tau  in
               divide FStar_BigInt.one tau uu____3144  in
             bind uu____3135
               (fun uu____3162  ->
                  match uu____3162 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3203 =
        bind t1
          (fun uu____3208  ->
             let uu____3209 = map t2  in
             bind uu____3209 (fun uu____3217  -> ret ()))
         in
      focus uu____3203
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3226  ->
    let uu____3229 =
      let uu____3232 = cur_goal ()  in
      bind uu____3232
        (fun goal  ->
           let uu____3241 =
             let uu____3248 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3248  in
           match uu____3241 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3257 =
                 let uu____3258 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3258  in
               if uu____3257
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3263 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3263 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3277 = new_uvar "intro" env' typ'  in
                  bind uu____3277
                    (fun uu____3293  ->
                       match uu____3293 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3317 = set_solution goal sol  in
                           bind uu____3317
                             (fun uu____3323  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3325 =
                                  let uu____3328 = bnorm_goal g  in
                                  replace_cur uu____3328  in
                                bind uu____3325 (fun uu____3330  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3335 =
                 let uu____3336 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3337 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3336 uu____3337  in
               fail1 "goal is not an arrow (%s)" uu____3335)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3229
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3352  ->
    let uu____3359 = cur_goal ()  in
    bind uu____3359
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3376 =
            let uu____3383 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3383  in
          match uu____3376 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3396 =
                let uu____3397 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3397  in
              if uu____3396
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3410 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3410
                    in
                 let bs =
                   let uu____3420 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3420; b]  in
                 let env' =
                   let uu____3446 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3446 bs  in
                 let uu____3447 =
                   let uu____3454 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3454  in
                 bind uu____3447
                   (fun uu____3473  ->
                      match uu____3473 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3487 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3490 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3487
                              FStar_Parser_Const.effect_Tot_lid uu____3490 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3508 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3508 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3530 =
                                   let uu____3531 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3531.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3530
                                  in
                               let uu____3544 = set_solution goal tm  in
                               bind uu____3544
                                 (fun uu____3553  ->
                                    let uu____3554 =
                                      let uu____3557 =
                                        bnorm_goal
                                          (let uu___397_3560 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___397_3560.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___397_3560.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___397_3560.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___397_3560.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____3557  in
                                    bind uu____3554
                                      (fun uu____3567  ->
                                         let uu____3568 =
                                           let uu____3573 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3573, b)  in
                                         ret uu____3568)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3582 =
                let uu____3583 = FStar_Tactics_Types.goal_env goal  in
                let uu____3584 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3583 uu____3584  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3582))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3602 = cur_goal ()  in
    bind uu____3602
      (fun goal  ->
         mlog
           (fun uu____3609  ->
              let uu____3610 =
                let uu____3611 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3611  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3610)
           (fun uu____3616  ->
              let steps =
                let uu____3620 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3620
                 in
              let t =
                let uu____3624 = FStar_Tactics_Types.goal_env goal  in
                let uu____3625 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3624 uu____3625  in
              let uu____3626 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3626))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3650 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____3658 -> g.FStar_Tactics_Types.opts
                 | uu____3661 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____3666  ->
                    let uu____3667 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____3667)
                 (fun uu____3670  ->
                    let uu____3671 = __tc_lax e t  in
                    bind uu____3671
                      (fun uu____3692  ->
                         match uu____3692 with
                         | (t1,uu____3702,uu____3703) ->
                             let steps =
                               let uu____3707 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____3707
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____3713  ->
                                  let uu____3714 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____3714)
                               (fun uu____3716  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3650
  
let (refine_intro : unit -> unit tac) =
  fun uu____3727  ->
    let uu____3730 =
      let uu____3733 = cur_goal ()  in
      bind uu____3733
        (fun g  ->
           let uu____3740 =
             let uu____3751 = FStar_Tactics_Types.goal_env g  in
             let uu____3752 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3751 uu____3752
              in
           match uu____3740 with
           | (uu____3755,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3780 =
                 let uu____3785 =
                   let uu____3790 =
                     let uu____3791 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3791]  in
                   FStar_Syntax_Subst.open_term uu____3790 phi  in
                 match uu____3785 with
                 | (bvs,phi1) ->
                     let uu____3816 =
                       let uu____3817 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3817  in
                     (uu____3816, phi1)
                  in
               (match uu____3780 with
                | (bv1,phi1) ->
                    let uu____3836 =
                      let uu____3839 = FStar_Tactics_Types.goal_env g  in
                      let uu____3840 =
                        let uu____3841 =
                          let uu____3844 =
                            let uu____3845 =
                              let uu____3852 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3852)  in
                            FStar_Syntax_Syntax.NT uu____3845  in
                          [uu____3844]  in
                        FStar_Syntax_Subst.subst uu____3841 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3839
                        uu____3840 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____3836
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3860  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3730
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3879 = cur_goal ()  in
      bind uu____3879
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3887 = FStar_Tactics_Types.goal_env goal  in
               let uu____3888 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3887 uu____3888
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3890 = __tc env t  in
           bind uu____3890
             (fun uu____3909  ->
                match uu____3909 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3924  ->
                         let uu____3925 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3926 =
                           let uu____3927 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3927
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3925 uu____3926)
                      (fun uu____3930  ->
                         let uu____3931 =
                           let uu____3934 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3934 guard  in
                         bind uu____3931
                           (fun uu____3936  ->
                              mlog
                                (fun uu____3940  ->
                                   let uu____3941 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3942 =
                                     let uu____3943 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3943
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3941 uu____3942)
                                (fun uu____3946  ->
                                   let uu____3947 =
                                     let uu____3950 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3951 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3950 typ uu____3951  in
                                   bind uu____3947
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3957 =
                                             let uu____3958 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3958 t1  in
                                           let uu____3959 =
                                             let uu____3960 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3960 typ  in
                                           let uu____3961 =
                                             let uu____3962 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3963 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3962 uu____3963  in
                                           let uu____3964 =
                                             let uu____3965 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3966 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3965 uu____3966  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3957 uu____3959 uu____3961
                                             uu____3964)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____3986 =
          mlog
            (fun uu____3991  ->
               let uu____3992 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____3992)
            (fun uu____3995  ->
               let uu____3996 =
                 let uu____4003 = __exact_now set_expected_typ1 tm  in
                 catch uu____4003  in
               bind uu____3996
                 (fun uu___352_4012  ->
                    match uu___352_4012 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        fail e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4023  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4026  ->
                             let uu____4027 =
                               let uu____4034 =
                                 let uu____4037 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4037
                                   (fun uu____4042  ->
                                      let uu____4043 = refine_intro ()  in
                                      bind uu____4043
                                        (fun uu____4047  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4034  in
                             bind uu____4027
                               (fun uu___351_4054  ->
                                  match uu___351_4054 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4063  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4065  -> ret ())
                                  | FStar_Util.Inl uu____4066 ->
                                      mlog
                                        (fun uu____4068  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4070  -> fail e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____3986
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4120 = f x  in
          bind uu____4120
            (fun y  ->
               let uu____4128 = mapM f xs  in
               bind uu____4128 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4199 = do_unify e ty1 ty2  in
          bind uu____4199
            (fun uu___353_4211  ->
               if uu___353_4211
               then ret acc
               else
                 (let uu____4230 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4230 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4251 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4252 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4251
                        uu____4252
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4267 =
                        let uu____4268 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4268  in
                      if uu____4267
                      then fail "Codomain is effectful"
                      else
                        (let uu____4288 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4288
                           (fun uu____4314  ->
                              match uu____4314 with
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
      let uu____4400 =
        mlog
          (fun uu____4405  ->
             let uu____4406 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____4406)
          (fun uu____4409  ->
             let uu____4410 = cur_goal ()  in
             bind uu____4410
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4418 = __tc e tm  in
                  bind uu____4418
                    (fun uu____4439  ->
                       match uu____4439 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4452 =
                             let uu____4463 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4463  in
                           bind uu____4452
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4506  ->
                                       fun w  ->
                                         match uu____4506 with
                                         | (uvt,q,uu____4524) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4556 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4573  ->
                                       fun s  ->
                                         match uu____4573 with
                                         | (uu____4585,uu____4586,uv) ->
                                             let uu____4588 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4588) uvs uu____4556
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4597 = solve' goal w  in
                                bind uu____4597
                                  (fun uu____4602  ->
                                     let uu____4603 =
                                       mapM
                                         (fun uu____4620  ->
                                            match uu____4620 with
                                            | (uvt,q,uv) ->
                                                let uu____4632 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4632 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4637 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4638 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4638
                                                     then ret ()
                                                     else
                                                       (let uu____4642 =
                                                          let uu____4645 =
                                                            bnorm_goal
                                                              (let uu___398_4648
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___398_4648.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___398_4648.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___398_4648.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____4645]  in
                                                        add_goals uu____4642)))
                                         uvs
                                        in
                                     bind uu____4603
                                       (fun uu____4652  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4400
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4677 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4677
    then
      let uu____4684 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4699 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4752 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4684 with
      | (pre,post) ->
          let post1 =
            let uu____4784 =
              let uu____4795 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4795]  in
            FStar_Syntax_Util.mk_app post uu____4784  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4825 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4825
       then
         let uu____4832 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4832
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4865 =
      let uu____4868 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4875  ->
                  let uu____4876 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4876)
               (fun uu____4880  ->
                  let is_unit_t t =
                    let uu____4887 =
                      let uu____4888 = FStar_Syntax_Subst.compress t  in
                      uu____4888.FStar_Syntax_Syntax.n  in
                    match uu____4887 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4892 -> false  in
                  let uu____4893 = cur_goal ()  in
                  bind uu____4893
                    (fun goal  ->
                       let uu____4899 =
                         let uu____4908 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4908 tm  in
                       bind uu____4899
                         (fun uu____4923  ->
                            match uu____4923 with
                            | (tm1,t,guard) ->
                                let uu____4935 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4935 with
                                 | (bs,comp) ->
                                     let uu____4968 = lemma_or_sq comp  in
                                     (match uu____4968 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4987 =
                                            FStar_List.fold_left
                                              (fun uu____5035  ->
                                                 fun uu____5036  ->
                                                   match (uu____5035,
                                                           uu____5036)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5149 =
                                                         is_unit_t b_t  in
                                                       if uu____5149
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5187 =
                                                            let uu____5200 =
                                                              let uu____5201
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5201.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5204 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5200
                                                              uu____5204 b_t
                                                             in
                                                          match uu____5187
                                                          with
                                                          | (u,uu____5222,g_u)
                                                              ->
                                                              let uu____5236
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5236,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4987 with
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
                                               let uu____5315 =
                                                 let uu____5318 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5319 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5320 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5318
                                                   uu____5319 uu____5320
                                                  in
                                               bind uu____5315
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5328 =
                                                        let uu____5329 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5329 tm1
                                                         in
                                                      let uu____5330 =
                                                        let uu____5331 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5332 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5331
                                                          uu____5332
                                                         in
                                                      let uu____5333 =
                                                        let uu____5334 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5335 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5334
                                                          uu____5335
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5328 uu____5330
                                                        uu____5333
                                                    else
                                                      (let uu____5337 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5337
                                                         (fun uu____5342  ->
                                                            let uu____5343 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5343
                                                              (fun uu____5351
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5376
                                                                    =
                                                                    let uu____5379
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5379
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5376
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
                                                                    let uu____5414
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5414)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5430
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5430
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5448)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5474)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5491
                                                                    -> false)
                                                                    in
                                                                 let uu____5492
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
                                                                    let uu____5522
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5522
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5544)
                                                                    ->
                                                                    let uu____5569
                                                                    =
                                                                    let uu____5570
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5570.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5569
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5578)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___399_5598
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___399_5598.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___399_5598.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___399_5598.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___399_5598.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5601
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5607
                                                                     ->
                                                                    let uu____5608
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5609
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5608
                                                                    uu____5609)
                                                                    (fun
                                                                    uu____5614
                                                                     ->
                                                                    let env =
                                                                    let uu___400_5616
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___400_5616.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5618
                                                                    =
                                                                    let uu____5621
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5622
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5623
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5622
                                                                    uu____5623
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5625
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5621
                                                                    uu____5625
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5618
                                                                    (fun
                                                                    uu____5629
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5492
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
                                                                    let uu____5691
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5691
                                                                    then
                                                                    let uu____5694
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5694
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
                                                                    let uu____5708
                                                                    =
                                                                    let uu____5709
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5709
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5708)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5710
                                                                    =
                                                                    let uu____5713
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5713
                                                                    guard  in
                                                                    bind
                                                                    uu____5710
                                                                    (fun
                                                                    uu____5716
                                                                     ->
                                                                    let uu____5717
                                                                    =
                                                                    let uu____5720
                                                                    =
                                                                    let uu____5721
                                                                    =
                                                                    let uu____5722
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5723
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5722
                                                                    uu____5723
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5721
                                                                     in
                                                                    if
                                                                    uu____5720
                                                                    then
                                                                    let uu____5726
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5726
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5717
                                                                    (fun
                                                                    uu____5729
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4868  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4865
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5751 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5751 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5761::(e1,uu____5763)::(e2,uu____5765)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____5826 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5850 = destruct_eq' typ  in
    match uu____5850 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5880 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5880 with
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
        let uu____5948 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5948 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____6004 = aux e'  in
               FStar_Util.map_opt uu____6004
                 (fun uu____6035  ->
                    match uu____6035 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____6061 = aux e  in
      FStar_Util.map_opt uu____6061
        (fun uu____6092  ->
           match uu____6092 with
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
          let uu____6164 =
            let uu____6175 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6175  in
          FStar_Util.map_opt uu____6164
            (fun uu____6193  ->
               match uu____6193 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___401_6215 = bv  in
                     let uu____6216 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___401_6215.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___401_6215.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6216
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___402_6224 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6225 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6234 =
                       let uu____6237 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6237  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___402_6224.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6225;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6234;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___402_6224.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___402_6224.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___402_6224.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___403_6238 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___403_6238.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___403_6238.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___403_6238.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___403_6238.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6248 =
      let uu____6251 = cur_goal ()  in
      bind uu____6251
        (fun goal  ->
           let uu____6259 = h  in
           match uu____6259 with
           | (bv,uu____6263) ->
               mlog
                 (fun uu____6271  ->
                    let uu____6272 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6273 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6272
                      uu____6273)
                 (fun uu____6276  ->
                    let uu____6277 =
                      let uu____6288 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6288  in
                    match uu____6277 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____6314 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____6314 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6329 =
                               let uu____6330 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6330.FStar_Syntax_Syntax.n  in
                             (match uu____6329 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___404_6347 = bv2  in
                                    let uu____6348 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___404_6347.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___404_6347.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6348
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___405_6356 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6357 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6366 =
                                      let uu____6369 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6369
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___405_6356.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6357;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6366;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___405_6356.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___405_6356.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___405_6356.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___406_6372 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___406_6372.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___406_6372.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___406_6372.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___406_6372.FStar_Tactics_Types.label)
                                     })
                              | uu____6373 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6374 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6248
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6399 =
        let uu____6402 = cur_goal ()  in
        bind uu____6402
          (fun goal  ->
             let uu____6413 = b  in
             match uu____6413 with
             | (bv,uu____6417) ->
                 let bv' =
                   let uu____6423 =
                     let uu___407_6424 = bv  in
                     let uu____6425 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6425;
                       FStar_Syntax_Syntax.index =
                         (uu___407_6424.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___407_6424.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6423  in
                 let s1 =
                   let uu____6429 =
                     let uu____6430 =
                       let uu____6437 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6437)  in
                     FStar_Syntax_Syntax.NT uu____6430  in
                   [uu____6429]  in
                 let uu____6442 = subst_goal bv bv' s1 goal  in
                 (match uu____6442 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6399
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6461 =
      let uu____6464 = cur_goal ()  in
      bind uu____6464
        (fun goal  ->
           let uu____6473 = b  in
           match uu____6473 with
           | (bv,uu____6477) ->
               let uu____6482 =
                 let uu____6493 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6493  in
               (match uu____6482 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____6519 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6519 with
                     | (ty,u) ->
                         let uu____6528 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6528
                           (fun uu____6546  ->
                              match uu____6546 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___408_6556 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___408_6556.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___408_6556.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6560 =
                                      let uu____6561 =
                                        let uu____6568 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____6568)  in
                                      FStar_Syntax_Syntax.NT uu____6561  in
                                    [uu____6560]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___409_6580 = b1  in
                                         let uu____6581 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___409_6580.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___409_6580.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6581
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6588  ->
                                       let new_goal =
                                         let uu____6590 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6591 =
                                           let uu____6592 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6592
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6590 uu____6591
                                          in
                                       let uu____6593 = add_goals [new_goal]
                                          in
                                       bind uu____6593
                                         (fun uu____6598  ->
                                            let uu____6599 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6599
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6461
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6622 =
        let uu____6625 = cur_goal ()  in
        bind uu____6625
          (fun goal  ->
             let uu____6634 = b  in
             match uu____6634 with
             | (bv,uu____6638) ->
                 let uu____6643 =
                   let uu____6654 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6654  in
                 (match uu____6643 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____6683 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6683
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___410_6688 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___410_6688.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___410_6688.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6690 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6690))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6622
  
let (revert : unit -> unit tac) =
  fun uu____6701  ->
    let uu____6704 = cur_goal ()  in
    bind uu____6704
      (fun goal  ->
         let uu____6710 =
           let uu____6717 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6717  in
         match uu____6710 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6733 =
                 let uu____6736 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6736  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6733
                in
             let uu____6751 = new_uvar "revert" env' typ'  in
             bind uu____6751
               (fun uu____6766  ->
                  match uu____6766 with
                  | (r,u_r) ->
                      let uu____6775 =
                        let uu____6778 =
                          let uu____6779 =
                            let uu____6780 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6780.FStar_Syntax_Syntax.pos  in
                          let uu____6783 =
                            let uu____6788 =
                              let uu____6789 =
                                let uu____6798 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6798  in
                              [uu____6789]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6788  in
                          uu____6783 FStar_Pervasives_Native.None uu____6779
                           in
                        set_solution goal uu____6778  in
                      bind uu____6775
                        (fun uu____6819  ->
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
      let uu____6831 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6831
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6846 = cur_goal ()  in
    bind uu____6846
      (fun goal  ->
         mlog
           (fun uu____6854  ->
              let uu____6855 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6856 =
                let uu____6857 =
                  let uu____6858 =
                    let uu____6867 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6867  in
                  FStar_All.pipe_right uu____6858 FStar_List.length  in
                FStar_All.pipe_right uu____6857 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6855 uu____6856)
           (fun uu____6884  ->
              let uu____6885 =
                let uu____6896 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6896  in
              match uu____6885 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6940 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6940
                        then
                          let uu____6943 =
                            let uu____6944 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6944
                             in
                          fail uu____6943
                        else check1 bvs2
                     in
                  let uu____6946 =
                    let uu____6947 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____6947  in
                  if uu____6946
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6951 = check1 bvs  in
                     bind uu____6951
                       (fun uu____6957  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6959 =
                            let uu____6966 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6966  in
                          bind uu____6959
                            (fun uu____6975  ->
                               match uu____6975 with
                               | (ut,uvar_ut) ->
                                   let uu____6984 = set_solution goal ut  in
                                   bind uu____6984
                                     (fun uu____6989  ->
                                        let uu____6990 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____6990))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6997  ->
    let uu____7000 = cur_goal ()  in
    bind uu____7000
      (fun goal  ->
         let uu____7006 =
           let uu____7013 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7013  in
         match uu____7006 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____7021) ->
             let uu____7026 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____7026)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____7036 = cur_goal ()  in
    bind uu____7036
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7046 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7046  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7049  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____7059 = cur_goal ()  in
    bind uu____7059
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7069 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7069  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7072  -> add_goals [g']))
  
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
            let uu____7112 = FStar_Syntax_Subst.compress t  in
            uu____7112.FStar_Syntax_Syntax.n  in
          let uu____7115 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___414_7121 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___414_7121.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___414_7121.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____7115
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7137 =
                   let uu____7138 = FStar_Syntax_Subst.compress t1  in
                   uu____7138.FStar_Syntax_Syntax.n  in
                 match uu____7137 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____7169 = ff hd1  in
                     bind uu____7169
                       (fun hd2  ->
                          let fa uu____7195 =
                            match uu____7195 with
                            | (a,q) ->
                                let uu____7216 = ff a  in
                                bind uu____7216 (fun a1  -> ret (a1, q))
                             in
                          let uu____7235 = mapM fa args  in
                          bind uu____7235
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7317 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7317 with
                      | (bs1,t') ->
                          let uu____7326 =
                            let uu____7329 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7329 t'  in
                          bind uu____7326
                            (fun t''  ->
                               let uu____7333 =
                                 let uu____7334 =
                                   let uu____7353 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7362 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7353, uu____7362, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7334  in
                               ret uu____7333))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7437 = ff hd1  in
                     bind uu____7437
                       (fun hd2  ->
                          let ffb br =
                            let uu____7452 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7452 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7484 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7484  in
                                let uu____7485 = ff1 e  in
                                bind uu____7485
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7500 = mapM ffb brs  in
                          bind uu____7500
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7544;
                          FStar_Syntax_Syntax.lbtyp = uu____7545;
                          FStar_Syntax_Syntax.lbeff = uu____7546;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7548;
                          FStar_Syntax_Syntax.lbpos = uu____7549;_}::[]),e)
                     ->
                     let lb =
                       let uu____7574 =
                         let uu____7575 = FStar_Syntax_Subst.compress t1  in
                         uu____7575.FStar_Syntax_Syntax.n  in
                       match uu____7574 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7579) -> lb
                       | uu____7592 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7601 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7601
                         (fun def1  ->
                            ret
                              (let uu___411_7607 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___411_7607.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___411_7607.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___411_7607.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___411_7607.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___411_7607.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___411_7607.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7608 = fflb lb  in
                     bind uu____7608
                       (fun lb1  ->
                          let uu____7618 =
                            let uu____7623 =
                              let uu____7624 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7624]  in
                            FStar_Syntax_Subst.open_term uu____7623 e  in
                          match uu____7618 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7654 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7654  in
                              let uu____7655 = ff1 e1  in
                              bind uu____7655
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7696 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7696
                         (fun def  ->
                            ret
                              (let uu___412_7702 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___412_7702.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___412_7702.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___412_7702.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___412_7702.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___412_7702.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___412_7702.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7703 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7703 with
                      | (lbs1,e1) ->
                          let uu____7718 = mapM fflb lbs1  in
                          bind uu____7718
                            (fun lbs2  ->
                               let uu____7730 = ff e1  in
                               bind uu____7730
                                 (fun e2  ->
                                    let uu____7738 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7738 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7806 = ff t2  in
                     bind uu____7806
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7837 = ff t2  in
                     bind uu____7837
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7844 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___413_7851 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___413_7851.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___413_7851.FStar_Syntax_Syntax.vars)
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
              let uu____7893 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___415_7902 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___415_7902.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___415_7902.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___415_7902.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___415_7902.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___415_7902.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___415_7902.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___415_7902.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___415_7902.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___415_7902.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___415_7902.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___415_7902.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___415_7902.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___415_7902.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___415_7902.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___415_7902.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___415_7902.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___415_7902.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___415_7902.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___415_7902.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___415_7902.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___415_7902.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___415_7902.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___415_7902.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___415_7902.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___415_7902.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___415_7902.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___415_7902.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___415_7902.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___415_7902.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___415_7902.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___415_7902.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___415_7902.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___415_7902.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___415_7902.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___415_7902.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___415_7902.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___415_7902.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___415_7902.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___415_7902.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___415_7902.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___415_7902.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___415_7902.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____7893 with
              | (t1,lcomp,g) ->
                  let uu____7908 =
                    (let uu____7911 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____7911) ||
                      (let uu____7913 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____7913)
                     in
                  if uu____7908
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____7921 = new_uvar "pointwise_rec" env typ  in
                       bind uu____7921
                         (fun uu____7937  ->
                            match uu____7937 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____7950  ->
                                      let uu____7951 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____7952 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____7951 uu____7952);
                                 (let uu____7953 =
                                    let uu____7956 =
                                      let uu____7957 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____7957 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____7956
                                      opts label1
                                     in
                                  bind uu____7953
                                    (fun uu____7960  ->
                                       let uu____7961 =
                                         bind tau
                                           (fun uu____7967  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____7973  ->
                                                   let uu____7974 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____7975 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____7974 uu____7975);
                                              ret ut1)
                                          in
                                       focus uu____7961))))
                        in
                     let uu____7976 = catch rewrite_eq  in
                     bind uu____7976
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
          let uu____8174 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____8174
            (fun t1  ->
               let uu____8182 =
                 f env
                   (let uu___418_8191 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___418_8191.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___418_8191.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____8182
                 (fun uu____8207  ->
                    match uu____8207 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____8230 =
                               let uu____8231 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____8231.FStar_Syntax_Syntax.n  in
                             match uu____8230 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8268 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8268
                                   (fun uu____8293  ->
                                      match uu____8293 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8309 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8309
                                            (fun uu____8336  ->
                                               match uu____8336 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___416_8366 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___416_8366.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___416_8366.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8408 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8408 with
                                  | (bs1,t') ->
                                      let uu____8423 =
                                        let uu____8430 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8430 ctrl1 t'
                                         in
                                      bind uu____8423
                                        (fun uu____8448  ->
                                           match uu____8448 with
                                           | (t'',ctrl2) ->
                                               let uu____8463 =
                                                 let uu____8470 =
                                                   let uu___417_8473 = t4  in
                                                   let uu____8476 =
                                                     let uu____8477 =
                                                       let uu____8496 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8505 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8496,
                                                         uu____8505, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8477
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8476;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___417_8473.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___417_8473.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8470, ctrl2)  in
                                               ret uu____8463))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8558 -> ret (t3, ctrl1))))

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
              let uu____8605 = ctrl_tac_fold f env ctrl t  in
              bind uu____8605
                (fun uu____8629  ->
                   match uu____8629 with
                   | (t1,ctrl1) ->
                       let uu____8644 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8644
                         (fun uu____8671  ->
                            match uu____8671 with
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
                let uu____8760 =
                  let uu____8767 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____8767
                    (fun uu____8776  ->
                       let uu____8777 = ctrl t1  in
                       bind uu____8777
                         (fun res  ->
                            let uu____8800 = trivial ()  in
                            bind uu____8800 (fun uu____8808  -> ret res)))
                   in
                bind uu____8760
                  (fun uu____8824  ->
                     match uu____8824 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____8848 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___419_8857 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___419_8857.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___419_8857.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___419_8857.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___419_8857.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___419_8857.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___419_8857.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___419_8857.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___419_8857.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___419_8857.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___419_8857.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___419_8857.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___419_8857.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___419_8857.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___419_8857.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___419_8857.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___419_8857.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___419_8857.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___419_8857.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___419_8857.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___419_8857.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___419_8857.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___419_8857.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___419_8857.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___419_8857.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___419_8857.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___419_8857.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___419_8857.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___419_8857.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___419_8857.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___419_8857.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___419_8857.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___419_8857.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___419_8857.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___419_8857.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___419_8857.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___419_8857.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___419_8857.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___419_8857.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___419_8857.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___419_8857.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___419_8857.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___419_8857.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____8848 with
                            | (t2,lcomp,g) ->
                                let uu____8867 =
                                  (let uu____8870 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____8870) ||
                                    (let uu____8872 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____8872)
                                   in
                                if uu____8867
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____8885 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____8885
                                     (fun uu____8905  ->
                                        match uu____8905 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____8922  ->
                                                  let uu____8923 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____8924 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____8923 uu____8924);
                                             (let uu____8925 =
                                                let uu____8928 =
                                                  let uu____8929 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____8929 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____8928 opts label1
                                                 in
                                              bind uu____8925
                                                (fun uu____8936  ->
                                                   let uu____8937 =
                                                     bind rewriter
                                                       (fun uu____8951  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____8957 
                                                               ->
                                                               let uu____8958
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____8959
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____8958
                                                                 uu____8959);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____8937)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____9000 =
        bind get
          (fun ps  ->
             let uu____9010 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9010 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9047  ->
                       let uu____9048 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____9048);
                  bind dismiss_all
                    (fun uu____9051  ->
                       let uu____9052 =
                         let uu____9059 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9059
                           keepGoing gt1
                          in
                       bind uu____9052
                         (fun uu____9071  ->
                            match uu____9071 with
                            | (gt',uu____9079) ->
                                (log ps
                                   (fun uu____9083  ->
                                      let uu____9084 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____9084);
                                 (let uu____9085 = push_goals gs  in
                                  bind uu____9085
                                    (fun uu____9090  ->
                                       let uu____9091 =
                                         let uu____9094 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____9094]  in
                                       add_goals uu____9091)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____9000
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____9117 =
        bind get
          (fun ps  ->
             let uu____9127 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9127 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9164  ->
                       let uu____9165 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____9165);
                  bind dismiss_all
                    (fun uu____9168  ->
                       let uu____9169 =
                         let uu____9172 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9172 gt1
                          in
                       bind uu____9169
                         (fun gt'  ->
                            log ps
                              (fun uu____9180  ->
                                 let uu____9181 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____9181);
                            (let uu____9182 = push_goals gs  in
                             bind uu____9182
                               (fun uu____9187  ->
                                  let uu____9188 =
                                    let uu____9191 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____9191]  in
                                  add_goals uu____9188))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____9117
  
let (trefl : unit -> unit tac) =
  fun uu____9202  ->
    let uu____9205 =
      let uu____9208 = cur_goal ()  in
      bind uu____9208
        (fun g  ->
           let uu____9226 =
             let uu____9231 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____9231  in
           match uu____9226 with
           | FStar_Pervasives_Native.Some t ->
               let uu____9239 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____9239 with
                | (hd1,args) ->
                    let uu____9278 =
                      let uu____9291 =
                        let uu____9292 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9292.FStar_Syntax_Syntax.n  in
                      (uu____9291, args)  in
                    (match uu____9278 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9306::(l,uu____9308)::(r,uu____9310)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9357 =
                           let uu____9360 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9360 l r  in
                         bind uu____9357
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9367 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9367 l
                                    in
                                 let r1 =
                                   let uu____9369 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9369 r
                                    in
                                 let uu____9370 =
                                   let uu____9373 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9373 l1 r1  in
                                 bind uu____9370
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9379 =
                                           let uu____9380 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9380 l1  in
                                         let uu____9381 =
                                           let uu____9382 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9382 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9379 uu____9381))))
                     | (hd2,uu____9384) ->
                         let uu____9401 =
                           let uu____9402 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9402 t  in
                         fail1 "trefl: not an equality (%s)" uu____9401))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____9205
  
let (dup : unit -> unit tac) =
  fun uu____9415  ->
    let uu____9418 = cur_goal ()  in
    bind uu____9418
      (fun g  ->
         let uu____9424 =
           let uu____9431 = FStar_Tactics_Types.goal_env g  in
           let uu____9432 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9431 uu____9432  in
         bind uu____9424
           (fun uu____9441  ->
              match uu____9441 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___420_9451 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___420_9451.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___420_9451.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___420_9451.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___420_9451.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____9454  ->
                       let uu____9455 =
                         let uu____9458 = FStar_Tactics_Types.goal_env g  in
                         let uu____9459 =
                           let uu____9460 =
                             let uu____9461 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9462 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9461
                               uu____9462
                              in
                           let uu____9463 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9464 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9460 uu____9463 u
                             uu____9464
                            in
                         add_irrelevant_goal "dup equation" uu____9458
                           uu____9459 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____9455
                         (fun uu____9467  ->
                            let uu____9468 = add_goals [g']  in
                            bind uu____9468 (fun uu____9472  -> ret ())))))
  
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
              let uu____9595 = f x y  in
              if uu____9595 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____9615 -> (acc, l11, l21)  in
        let uu____9630 = aux [] l1 l2  in
        match uu____9630 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____9735 = get_phi g1  in
      match uu____9735 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____9741 = get_phi g2  in
          (match uu____9741 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____9753 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____9753 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____9784 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____9784 phi1  in
                    let t2 =
                      let uu____9794 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____9794 phi2  in
                    let uu____9803 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____9803
                      (fun uu____9808  ->
                         let uu____9809 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____9809
                           (fun uu____9816  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___421_9821 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____9822 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___421_9821.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___421_9821.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___421_9821.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___421_9821.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____9822;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___421_9821.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___421_9821.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___421_9821.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___421_9821.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___421_9821.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___421_9821.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___421_9821.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___421_9821.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___421_9821.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___421_9821.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___421_9821.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___421_9821.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___421_9821.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___421_9821.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___421_9821.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___421_9821.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___421_9821.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___421_9821.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___421_9821.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___421_9821.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___421_9821.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___421_9821.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___421_9821.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___421_9821.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___421_9821.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___421_9821.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___421_9821.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___421_9821.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___421_9821.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___421_9821.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___421_9821.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___421_9821.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___421_9821.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___421_9821.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___421_9821.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___421_9821.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___421_9821.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____9825 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____9825
                                (fun goal  ->
                                   mlog
                                     (fun uu____9834  ->
                                        let uu____9835 =
                                          goal_to_string_verbose g1  in
                                        let uu____9836 =
                                          goal_to_string_verbose g2  in
                                        let uu____9837 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____9835 uu____9836 uu____9837)
                                     (fun uu____9839  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____9846  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____9862 =
               set
                 (let uu___422_9867 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___422_9867.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___422_9867.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___422_9867.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___422_9867.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___422_9867.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___422_9867.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___422_9867.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___422_9867.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___422_9867.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___422_9867.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___422_9867.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___422_9867.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____9862
               (fun uu____9870  ->
                  let uu____9871 = join_goals g1 g2  in
                  bind uu____9871 (fun g12  -> add_goals [g12]))
         | uu____9876 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9896 =
      let uu____9903 = cur_goal ()  in
      bind uu____9903
        (fun g  ->
           let uu____9913 =
             let uu____9922 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9922 t  in
           bind uu____9913
             (fun uu____9950  ->
                match uu____9950 with
                | (t1,typ,guard) ->
                    let uu____9966 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9966 with
                     | (hd1,args) ->
                         let uu____10015 =
                           let uu____10030 =
                             let uu____10031 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____10031.FStar_Syntax_Syntax.n  in
                           (uu____10030, args)  in
                         (match uu____10015 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____10052)::(q,uu____10054)::[]) when
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
                                let uu____10108 =
                                  let uu____10109 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____10109
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____10108
                                 in
                              let g2 =
                                let uu____10111 =
                                  let uu____10112 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____10112
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____10111
                                 in
                              bind __dismiss
                                (fun uu____10119  ->
                                   let uu____10120 = add_goals [g1; g2]  in
                                   bind uu____10120
                                     (fun uu____10129  ->
                                        let uu____10130 =
                                          let uu____10135 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____10136 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____10135, uu____10136)  in
                                        ret uu____10130))
                          | uu____10141 ->
                              let uu____10156 =
                                let uu____10157 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____10157 typ  in
                              fail1 "Not a disjunction: %s" uu____10156))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9896
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____10187 =
      let uu____10190 = cur_goal ()  in
      bind uu____10190
        (fun g  ->
           FStar_Options.push ();
           (let uu____10203 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____10203);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___423_10210 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___423_10210.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___423_10210.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___423_10210.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___423_10210.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____10187
  
let (top_env : unit -> env tac) =
  fun uu____10222  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____10235  ->
    let uu____10238 = cur_goal ()  in
    bind uu____10238
      (fun g  ->
         let uu____10244 =
           (FStar_Options.lax ()) ||
             (let uu____10246 = FStar_Tactics_Types.goal_env g  in
              uu____10246.FStar_TypeChecker_Env.lax)
            in
         ret uu____10244)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____10261 =
        mlog
          (fun uu____10266  ->
             let uu____10267 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____10267)
          (fun uu____10270  ->
             let uu____10271 = cur_goal ()  in
             bind uu____10271
               (fun goal  ->
                  let env =
                    let uu____10279 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____10279 ty  in
                  let uu____10280 = __tc_ghost env tm  in
                  bind uu____10280
                    (fun uu____10299  ->
                       match uu____10299 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____10313  ->
                                let uu____10314 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____10314)
                             (fun uu____10316  ->
                                mlog
                                  (fun uu____10319  ->
                                     let uu____10320 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____10320)
                                  (fun uu____10323  ->
                                     let uu____10324 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____10324
                                       (fun uu____10328  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____10261
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____10351 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____10357 =
              let uu____10364 =
                let uu____10365 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____10365
                 in
              new_uvar "uvar_env.2" env uu____10364  in
            bind uu____10357
              (fun uu____10381  ->
                 match uu____10381 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____10351
        (fun typ  ->
           let uu____10393 = new_uvar "uvar_env" env typ  in
           bind uu____10393
             (fun uu____10407  ->
                match uu____10407 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____10425 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____10444 -> g.FStar_Tactics_Types.opts
             | uu____10447 -> FStar_Options.peek ()  in
           let uu____10450 = FStar_Syntax_Util.head_and_args t  in
           match uu____10450 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____10470);
                FStar_Syntax_Syntax.pos = uu____10471;
                FStar_Syntax_Syntax.vars = uu____10472;_},uu____10473)
               ->
               let env1 =
                 let uu___424_10515 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___424_10515.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___424_10515.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___424_10515.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___424_10515.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___424_10515.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___424_10515.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___424_10515.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___424_10515.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___424_10515.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___424_10515.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___424_10515.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___424_10515.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___424_10515.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___424_10515.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___424_10515.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___424_10515.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___424_10515.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___424_10515.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___424_10515.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___424_10515.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___424_10515.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___424_10515.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___424_10515.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___424_10515.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___424_10515.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___424_10515.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___424_10515.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___424_10515.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___424_10515.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___424_10515.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___424_10515.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___424_10515.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___424_10515.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___424_10515.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___424_10515.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___424_10515.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___424_10515.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___424_10515.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___424_10515.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___424_10515.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___424_10515.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___424_10515.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____10517 =
                 let uu____10520 = bnorm_goal g  in [uu____10520]  in
               add_goals uu____10517
           | uu____10521 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____10425
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10570 = if b then t2 else ret false  in
             bind uu____10570 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10581 = trytac comp  in
      bind uu____10581
        (fun uu___354_10589  ->
           match uu___354_10589 with
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
        let uu____10615 =
          bind get
            (fun ps  ->
               let uu____10621 = __tc e t1  in
               bind uu____10621
                 (fun uu____10641  ->
                    match uu____10641 with
                    | (t11,ty1,g1) ->
                        let uu____10653 = __tc e t2  in
                        bind uu____10653
                          (fun uu____10673  ->
                             match uu____10673 with
                             | (t21,ty2,g2) ->
                                 let uu____10685 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10685
                                   (fun uu____10690  ->
                                      let uu____10691 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10691
                                        (fun uu____10697  ->
                                           let uu____10698 =
                                             do_unify e ty1 ty2  in
                                           let uu____10701 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10698 uu____10701)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10615
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10734  ->
             let uu____10735 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10735
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
        (fun uu____10756  ->
           let uu____10757 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10757)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10767 =
      mlog
        (fun uu____10772  ->
           let uu____10773 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10773)
        (fun uu____10776  ->
           let uu____10777 = cur_goal ()  in
           bind uu____10777
             (fun g  ->
                let uu____10783 =
                  let uu____10792 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10792 ty  in
                bind uu____10783
                  (fun uu____10804  ->
                     match uu____10804 with
                     | (ty1,uu____10814,guard) ->
                         let uu____10816 =
                           let uu____10819 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10819 guard  in
                         bind uu____10816
                           (fun uu____10822  ->
                              let uu____10823 =
                                let uu____10826 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10827 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10826 uu____10827 ty1  in
                              bind uu____10823
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10833 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10833
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____10839 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10840 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10839
                                          uu____10840
                                         in
                                      let nty =
                                        let uu____10842 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10842 ty1  in
                                      let uu____10843 =
                                        let uu____10846 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10846 ng nty  in
                                      bind uu____10843
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10852 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10852
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10767
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10915 =
      let uu____10924 = cur_goal ()  in
      bind uu____10924
        (fun g  ->
           let uu____10936 =
             let uu____10945 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10945 s_tm  in
           bind uu____10936
             (fun uu____10963  ->
                match uu____10963 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10981 =
                      let uu____10984 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10984 guard  in
                    bind uu____10981
                      (fun uu____10996  ->
                         let uu____10997 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10997 with
                         | (h,args) ->
                             let uu____11042 =
                               let uu____11049 =
                                 let uu____11050 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____11050.FStar_Syntax_Syntax.n  in
                               match uu____11049 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____11065;
                                      FStar_Syntax_Syntax.vars = uu____11066;_},us)
                                   -> ret (fv, us)
                               | uu____11076 -> fail "type is not an fv"  in
                             bind uu____11042
                               (fun uu____11096  ->
                                  match uu____11096 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____11112 =
                                        let uu____11115 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____11115 t_lid
                                         in
                                      (match uu____11112 with
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
                                                  (fun uu____11164  ->
                                                     let uu____11165 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____11165 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____11180 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____11208
                                                                  =
                                                                  let uu____11211
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____11211
                                                                    c_lid
                                                                   in
                                                                match uu____11208
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
                                                                    uu____11281
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
                                                                    let uu____11286
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____11286
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____11309
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____11309
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____11352
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____11352
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____11425
                                                                    =
                                                                    let uu____11426
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____11426
                                                                     in
                                                                    failwhen
                                                                    uu____11425
                                                                    "not total?"
                                                                    (fun
                                                                    uu____11443
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
                                                                    uu___355_11459
                                                                    =
                                                                    match uu___355_11459
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____11462)
                                                                    -> true
                                                                    | 
                                                                    uu____11463
                                                                    -> false
                                                                     in
                                                                    let uu____11466
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____11466
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
                                                                    uu____11599
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
                                                                    uu____11661
                                                                     ->
                                                                    match uu____11661
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11681),
                                                                    (t,uu____11683))
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
                                                                    uu____11751
                                                                     ->
                                                                    match uu____11751
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11777),
                                                                    (t,uu____11779))
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
                                                                    uu____11834
                                                                     ->
                                                                    match uu____11834
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
                                                                    let uu____11884
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___425_11901
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___425_11901.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____11884
                                                                    with
                                                                    | 
                                                                    (uu____11914,uu____11915,uu____11916,pat_t,uu____11918,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11925
                                                                    =
                                                                    let uu____11926
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11926
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11925
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11930
                                                                    =
                                                                    let uu____11939
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11939]
                                                                     in
                                                                    let uu____11958
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11930
                                                                    uu____11958
                                                                     in
                                                                    let nty =
                                                                    let uu____11964
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11964
                                                                     in
                                                                    let uu____11967
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11967
                                                                    (fun
                                                                    uu____11996
                                                                     ->
                                                                    match uu____11996
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
                                                                    let uu____12022
                                                                    =
                                                                    let uu____12033
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____12033]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____12022
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____12069
                                                                    =
                                                                    let uu____12080
                                                                    =
                                                                    let uu____12085
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____12085)
                                                                     in
                                                                    (g', br,
                                                                    uu____12080)
                                                                     in
                                                                    ret
                                                                    uu____12069))))))
                                                                    | 
                                                                    uu____12106
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____11180
                                                           (fun goal_brs  ->
                                                              let uu____12155
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____12155
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
                                                                  let uu____12228
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____12228
                                                                    (
                                                                    fun
                                                                    uu____12239
                                                                     ->
                                                                    let uu____12240
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____12240
                                                                    (fun
                                                                    uu____12250
                                                                     ->
                                                                    ret infos))))
                                            | uu____12257 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10915
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____12302::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____12330 = init xs  in x :: uu____12330
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____12342 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____12351) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____12416 = last args  in
          (match uu____12416 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____12446 =
                 let uu____12447 =
                   let uu____12452 =
                     let uu____12453 =
                       let uu____12458 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____12458  in
                     uu____12453 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____12452, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____12447  in
               FStar_All.pipe_left ret uu____12446)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____12471,uu____12472) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____12524 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____12524 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____12565 =
                      let uu____12566 =
                        let uu____12571 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____12571)  in
                      FStar_Reflection_Data.Tv_Abs uu____12566  in
                    FStar_All.pipe_left ret uu____12565))
      | FStar_Syntax_Syntax.Tm_type uu____12574 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____12598 ->
          let uu____12613 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____12613 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12643 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12643 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12696 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12708 =
            let uu____12709 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12709  in
          FStar_All.pipe_left ret uu____12708
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12730 =
            let uu____12731 =
              let uu____12736 =
                let uu____12737 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12737  in
              (uu____12736, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12731  in
          FStar_All.pipe_left ret uu____12730
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12771 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12776 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12776 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12829 ->
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
             | FStar_Util.Inr uu____12863 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12867 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12867 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12887 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12891 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12945 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12945
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12964 =
                  let uu____12971 =
                    FStar_List.map
                      (fun uu____12983  ->
                         match uu____12983 with
                         | (p1,uu____12991) -> inspect_pat p1) ps
                     in
                  (fv, uu____12971)  in
                FStar_Reflection_Data.Pat_Cons uu____12964
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
              (fun uu___356_13085  ->
                 match uu___356_13085 with
                 | (pat,uu____13107,t5) ->
                     let uu____13125 = inspect_pat pat  in (uu____13125, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____13134 ->
          ((let uu____13136 =
              let uu____13141 =
                let uu____13142 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____13143 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____13142 uu____13143
                 in
              (FStar_Errors.Warning_CantInspect, uu____13141)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____13136);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____12342
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____13156 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____13156
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____13160 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____13160
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____13164 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____13164
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____13171 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____13171
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____13196 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____13196
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____13213 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____13213
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____13232 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____13232
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____13236 =
          let uu____13237 =
            let uu____13244 =
              let uu____13245 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____13245  in
            FStar_Syntax_Syntax.mk uu____13244  in
          uu____13237 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13236
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____13253 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13253
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13262 =
          let uu____13263 =
            let uu____13270 =
              let uu____13271 =
                let uu____13284 =
                  let uu____13287 =
                    let uu____13288 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____13288]  in
                  FStar_Syntax_Subst.close uu____13287 t2  in
                ((false, [lb]), uu____13284)  in
              FStar_Syntax_Syntax.Tm_let uu____13271  in
            FStar_Syntax_Syntax.mk uu____13270  in
          uu____13263 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____13262
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____13328 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____13328 with
         | (lbs,body) ->
             let uu____13343 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____13343)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____13377 =
                let uu____13378 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____13378  in
              FStar_All.pipe_left wrap uu____13377
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____13385 =
                let uu____13386 =
                  let uu____13399 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____13415 = pack_pat p1  in
                         (uu____13415, false)) ps
                     in
                  (fv, uu____13399)  in
                FStar_Syntax_Syntax.Pat_cons uu____13386  in
              FStar_All.pipe_left wrap uu____13385
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
            (fun uu___357_13461  ->
               match uu___357_13461 with
               | (pat,t1) ->
                   let uu____13478 = pack_pat pat  in
                   (uu____13478, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____13526 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13526
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____13554 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13554
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____13600 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13600
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13639 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13639
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13656 =
        bind get
          (fun ps  ->
             let uu____13662 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13662 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13656
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13691 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___426_13698 = ps  in
                 let uu____13699 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___426_13698.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___426_13698.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___426_13698.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___426_13698.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___426_13698.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___426_13698.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___426_13698.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___426_13698.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___426_13698.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___426_13698.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___426_13698.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___426_13698.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13699
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13691
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13724 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13724 with
      | (u,ctx_uvars,g_u) ->
          let uu____13756 = FStar_List.hd ctx_uvars  in
          (match uu____13756 with
           | (ctx_uvar,uu____13770) ->
               let g =
                 let uu____13772 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13772 false
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
        let uu____13792 = goal_of_goal_ty env typ  in
        match uu____13792 with
        | (g,g_u) ->
            let ps =
              let uu____13804 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13805 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13804;
                FStar_Tactics_Types.local_state = uu____13805
              }  in
            let uu____13812 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13812)
  