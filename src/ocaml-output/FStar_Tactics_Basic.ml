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
    let uu____43 =
      let uu____44 = FStar_Tactics_Types.goal_env g  in
      let uu____45 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____44 uu____45  in
    FStar_Tactics_Types.goal_with_type g uu____43
  
type 'a tac =
  {
  tac_f: FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result }
let __proj__Mktac__item__tac_f :
  'a .
    'a tac ->
      FStar_Tactics_Types.proofstate -> 'a FStar_Tactics_Result.__result
  = fun projectee  -> match projectee with | { tac_f;_} -> tac_f 
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
      let uu____159 = FStar_Options.tactics_failhard ()  in
      if uu____159
      then run t p
      else
        (try (fun uu___369_169  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____178,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____182,msg,uu____184) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | e -> FStar_Tactics_Result.Failed (e, p))
  
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
           let uu____264 = run t1 p  in
           match uu____264 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____271 = t2 a  in run uu____271 q
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
    let uu____294 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____294 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____316 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____318 =
      let uu____320 = check_goal_solved g  in
      match uu____320 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____326 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____326
       in
    FStar_Util.format2 "%s%s\n" uu____316 uu____318
  
let (goal_to_string :
  Prims.string ->
    (Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      FStar_Tactics_Types.proofstate ->
        FStar_Tactics_Types.goal -> Prims.string)
  =
  fun kind  ->
    fun maybe_num  ->
      fun ps  ->
        fun g  ->
          let w =
            let uu____373 = FStar_Options.print_implicits ()  in
            if uu____373
            then
              let uu____377 = FStar_Tactics_Types.goal_env g  in
              let uu____378 = FStar_Tactics_Types.goal_witness g  in
              tts uu____377 uu____378
            else
              (let uu____381 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____381 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____387 = FStar_Tactics_Types.goal_env g  in
                   let uu____388 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____387 uu____388)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____411 = FStar_Util.string_of_int i  in
                let uu____413 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____411 uu____413
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.strcat " (" (Prims.strcat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____431 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____434 =
                 let uu____436 = FStar_Tactics_Types.goal_env g  in
                 tts uu____436
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____431 w uu____434)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____463 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____463
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____488 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____488
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____520 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____520
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____530) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____540) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____560 =
      let uu____561 = FStar_Tactics_Types.goal_env g  in
      let uu____562 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____561 uu____562  in
    FStar_Syntax_Util.un_squash uu____560
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____571 = get_phi g  in FStar_Option.isSome uu____571 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____595  ->
    bind get
      (fun ps  ->
         let uu____603 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____603)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____618  ->
    match uu____618 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____650 =
          let uu____654 =
            let uu____658 =
              let uu____660 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____660
                msg
               in
            let uu____663 =
              let uu____667 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____671 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____671
                else ""  in
              let uu____677 =
                let uu____681 =
                  let uu____683 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____683
                  then
                    let uu____688 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____688
                  else ""  in
                [uu____681]  in
              uu____667 :: uu____677  in
            uu____658 :: uu____663  in
          let uu____698 =
            let uu____702 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____722 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____702 uu____722  in
          FStar_List.append uu____654 uu____698  in
        FStar_String.concat "" uu____650
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____756 =
        let uu____757 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____757  in
      let uu____758 =
        let uu____763 =
          let uu____764 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____764  in
        FStar_Syntax_Print.binders_to_json uu____763  in
      FStar_All.pipe_right uu____756 uu____758  in
    let uu____765 =
      let uu____773 =
        let uu____781 =
          let uu____787 =
            let uu____788 =
              let uu____796 =
                let uu____802 =
                  let uu____803 =
                    let uu____805 = FStar_Tactics_Types.goal_env g  in
                    let uu____806 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____805 uu____806  in
                  FStar_Util.JsonStr uu____803  in
                ("witness", uu____802)  in
              let uu____809 =
                let uu____817 =
                  let uu____823 =
                    let uu____824 =
                      let uu____826 = FStar_Tactics_Types.goal_env g  in
                      let uu____827 = FStar_Tactics_Types.goal_type g  in
                      tts uu____826 uu____827  in
                    FStar_Util.JsonStr uu____824  in
                  ("type", uu____823)  in
                [uu____817;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____796 :: uu____809  in
            FStar_Util.JsonAssoc uu____788  in
          ("goal", uu____787)  in
        [uu____781]  in
      ("hyps", g_binders) :: uu____773  in
    FStar_Util.JsonAssoc uu____765
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____881  ->
    match uu____881 with
    | (msg,ps) ->
        let uu____891 =
          let uu____899 =
            let uu____907 =
              let uu____915 =
                let uu____923 =
                  let uu____929 =
                    let uu____930 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____930  in
                  ("goals", uu____929)  in
                let uu____935 =
                  let uu____943 =
                    let uu____949 =
                      let uu____950 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____950  in
                    ("smt-goals", uu____949)  in
                  [uu____943]  in
                uu____923 :: uu____935  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____915
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____907  in
          let uu____984 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____1000 =
                let uu____1006 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____1006)  in
              [uu____1000]
            else []  in
          FStar_List.append uu____899 uu____984  in
        FStar_Util.JsonAssoc uu____891
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1046  ->
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
         (let uu____1077 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____1077 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1150 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1150
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1164 . Prims.string -> Prims.string -> 'Auu____1164 tac =
  fun msg  ->
    fun x  -> let uu____1181 = FStar_Util.format1 msg x  in fail uu____1181
  
let fail2 :
  'Auu____1192 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1192 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1216 = FStar_Util.format2 msg x y  in fail uu____1216
  
let fail3 :
  'Auu____1229 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1229 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1260 = FStar_Util.format3 msg x y z  in fail uu____1260
  
let fail4 :
  'Auu____1275 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1275 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1313 = FStar_Util.format4 msg x y z w  in
            fail uu____1313
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1348 = run t ps  in
         match uu____1348 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___370_1372 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___370_1372.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___370_1372.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___370_1372.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___370_1372.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___370_1372.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___370_1372.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___370_1372.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___370_1372.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___370_1372.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___370_1372.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___370_1372.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___370_1372.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1411 = run t ps  in
         match uu____1411 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1459 = catch t  in
    bind uu____1459
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1486 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___372_1518  ->
              match () with
              | () -> let uu____1523 = trytac t  in run uu____1523 ps) ()
         with
         | FStar_Errors.Err (uu____1539,msg) ->
             (log ps
                (fun uu____1545  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1551,msg,uu____1553) ->
             (log ps
                (fun uu____1558  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1595 = run t ps  in
           match uu____1595 with
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
  fun p  -> mk_tac (fun uu____1619  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___373_1634 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___373_1634.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___373_1634.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___373_1634.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___373_1634.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___373_1634.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___373_1634.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___373_1634.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___373_1634.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___373_1634.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___373_1634.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___373_1634.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___373_1634.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1658 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1658
         then
           let uu____1662 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1664 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1662
             uu____1664
         else ());
        (try
           (fun uu___375_1675  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1683 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1683
                    then
                      let uu____1687 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1689 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1691 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1687
                        uu____1689 uu____1691
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1702 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1702 (fun uu____1707  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1717,msg) ->
             mlog
               (fun uu____1723  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1726  -> ret false)
         | FStar_Errors.Error (uu____1729,msg,r) ->
             mlog
               (fun uu____1737  ->
                  let uu____1738 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1738) (fun uu____1742  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___376_1756 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___376_1756.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___376_1756.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___376_1756.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___377_1759 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___377_1759.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___377_1759.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___377_1759.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___377_1759.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___377_1759.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___377_1759.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___377_1759.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___377_1759.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___377_1759.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___377_1759.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___377_1759.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___377_1759.FStar_Tactics_Types.local_state)
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
          (fun uu____1786  ->
             (let uu____1788 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1788
              then
                (FStar_Options.push ();
                 (let uu____1793 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1797 = __do_unify env t1 t2  in
              bind uu____1797
                (fun r  ->
                   (let uu____1808 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1808 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___378_1822 = ps  in
         let uu____1823 =
           FStar_List.filter
             (fun g  ->
                let uu____1829 = check_goal_solved g  in
                FStar_Option.isNone uu____1829) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___378_1822.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___378_1822.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___378_1822.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1823;
           FStar_Tactics_Types.smt_goals =
             (uu___378_1822.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___378_1822.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___378_1822.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___378_1822.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___378_1822.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___378_1822.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___378_1822.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___378_1822.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___378_1822.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1847 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1847 with
      | FStar_Pervasives_Native.Some uu____1852 ->
          let uu____1853 =
            let uu____1855 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1855  in
          fail uu____1853
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1876 = FStar_Tactics_Types.goal_env goal  in
      let uu____1877 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1876 solution uu____1877
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1884 =
         let uu___379_1885 = p  in
         let uu____1886 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___379_1885.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___379_1885.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___379_1885.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1886;
           FStar_Tactics_Types.smt_goals =
             (uu___379_1885.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___379_1885.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___379_1885.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___379_1885.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___379_1885.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___379_1885.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___379_1885.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___379_1885.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___379_1885.FStar_Tactics_Types.local_state)
         }  in
       set uu____1884)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1908  ->
           let uu____1909 =
             let uu____1911 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1911  in
           let uu____1912 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1909 uu____1912)
        (fun uu____1917  ->
           let uu____1918 = trysolve goal solution  in
           bind uu____1918
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1930  -> remove_solved_goals)
                else
                  (let uu____1933 =
                     let uu____1935 =
                       let uu____1937 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1937 solution  in
                     let uu____1938 =
                       let uu____1940 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1941 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1940 uu____1941  in
                     let uu____1942 =
                       let uu____1944 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1945 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1944 uu____1945  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1935 uu____1938 uu____1942
                      in
                   fail uu____1933)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1962 = set_solution goal solution  in
      bind uu____1962
        (fun uu____1966  ->
           bind __dismiss (fun uu____1968  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___380_1987 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___380_1987.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___380_1987.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___380_1987.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___380_1987.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___380_1987.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___380_1987.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___380_1987.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___380_1987.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___380_1987.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___380_1987.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___380_1987.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___380_1987.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___381_2006 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___381_2006.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___381_2006.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___381_2006.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___381_2006.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___381_2006.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___381_2006.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___381_2006.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___381_2006.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___381_2006.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___381_2006.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___381_2006.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___381_2006.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2033 = FStar_Options.defensive ()  in
    if uu____2033
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2043 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2043)
         in
      let b2 =
        b1 &&
          (let uu____2047 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2047)
         in
      let rec aux b3 e =
        let uu____2062 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2062 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2082 =
        (let uu____2086 = aux b2 env  in Prims.op_Negation uu____2086) &&
          (let uu____2089 = FStar_ST.op_Bang nwarn  in
           uu____2089 < (Prims.parse_int "5"))
         in
      (if uu____2082
       then
         ((let uu____2115 =
             let uu____2116 = FStar_Tactics_Types.goal_type g  in
             uu____2116.FStar_Syntax_Syntax.pos  in
           let uu____2119 =
             let uu____2125 =
               let uu____2127 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2127
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2125)  in
           FStar_Errors.log_issue uu____2115 uu____2119);
          (let uu____2131 =
             let uu____2133 = FStar_ST.op_Bang nwarn  in
             uu____2133 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____2131))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___382_2202 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___382_2202.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___382_2202.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___382_2202.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___382_2202.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___382_2202.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___382_2202.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___382_2202.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___382_2202.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___382_2202.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___382_2202.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___382_2202.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___382_2202.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___383_2223 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___383_2223.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___383_2223.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___383_2223.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___383_2223.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___383_2223.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___383_2223.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___383_2223.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___383_2223.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___383_2223.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___383_2223.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___383_2223.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___383_2223.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___384_2244 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___384_2244.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___384_2244.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___384_2244.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___384_2244.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___384_2244.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___384_2244.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___384_2244.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___384_2244.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___384_2244.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___384_2244.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___384_2244.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___384_2244.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___385_2265 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___385_2265.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___385_2265.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___385_2265.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___385_2265.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___385_2265.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___385_2265.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___385_2265.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___385_2265.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___385_2265.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___385_2265.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___385_2265.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___385_2265.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2277  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2308 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2308 with
        | (u,ctx_uvar,g_u) ->
            let uu____2346 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2346
              (fun uu____2355  ->
                 let uu____2356 =
                   let uu____2361 =
                     let uu____2362 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2362  in
                   (u, uu____2361)  in
                 ret uu____2356)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2383 = FStar_Syntax_Util.un_squash t1  in
    match uu____2383 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2395 =
          let uu____2396 = FStar_Syntax_Subst.compress t'1  in
          uu____2396.FStar_Syntax_Syntax.n  in
        (match uu____2395 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2401 -> false)
    | uu____2403 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2416 = FStar_Syntax_Util.un_squash t  in
    match uu____2416 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2427 =
          let uu____2428 = FStar_Syntax_Subst.compress t'  in
          uu____2428.FStar_Syntax_Syntax.n  in
        (match uu____2427 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2433 -> false)
    | uu____2435 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2448  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2460 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2460 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2467 = goal_to_string_verbose hd1  in
                    let uu____2469 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2467 uu____2469);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2482 =
      bind get
        (fun ps  ->
           let uu____2488 = cur_goal ()  in
           bind uu____2488
             (fun g  ->
                (let uu____2495 =
                   let uu____2496 = FStar_Tactics_Types.goal_type g  in
                   uu____2496.FStar_Syntax_Syntax.pos  in
                 let uu____2499 =
                   let uu____2505 =
                     let uu____2507 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2507
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2505)  in
                 FStar_Errors.log_issue uu____2495 uu____2499);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2482
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2530  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___386_2541 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___386_2541.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___386_2541.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___386_2541.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___386_2541.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___386_2541.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___386_2541.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___386_2541.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___386_2541.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___386_2541.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___386_2541.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___386_2541.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___386_2541.FStar_Tactics_Types.local_state)
           }  in
         let uu____2543 = set ps1  in
         bind uu____2543
           (fun uu____2548  ->
              let uu____2549 = FStar_BigInt.of_int_fs n1  in ret uu____2549))
  
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
              let uu____2587 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2587 phi  in
            let uu____2588 = new_uvar reason env typ  in
            bind uu____2588
              (fun uu____2603  ->
                 match uu____2603 with
                 | (uu____2610,ctx_uvar) ->
                     let goal =
                       FStar_Tactics_Types.mk_goal env ctx_uvar opts false
                         label1
                        in
                     ret goal)
  
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____2657  ->
                let uu____2658 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2658)
             (fun uu____2663  ->
                let e1 =
                  let uu___387_2665 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___387_2665.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___387_2665.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___387_2665.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___387_2665.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___387_2665.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___387_2665.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___387_2665.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___387_2665.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___387_2665.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___387_2665.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___387_2665.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___387_2665.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___387_2665.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___387_2665.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___387_2665.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___387_2665.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___387_2665.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___387_2665.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___387_2665.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___387_2665.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___387_2665.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___387_2665.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___387_2665.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___387_2665.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___387_2665.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___387_2665.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___387_2665.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___387_2665.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___387_2665.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___387_2665.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___387_2665.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___387_2665.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___387_2665.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___387_2665.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___387_2665.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___387_2665.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___387_2665.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___387_2665.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___387_2665.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___387_2665.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___387_2665.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___387_2665.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___389_2677  ->
                     match () with
                     | () ->
                         let uu____2686 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2686) ()
                with
                | FStar_Errors.Err (uu____2713,msg) ->
                    let uu____2717 = tts e1 t  in
                    let uu____2719 =
                      let uu____2721 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2721
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2717 uu____2719 msg
                | FStar_Errors.Error (uu____2731,msg,uu____2733) ->
                    let uu____2736 = tts e1 t  in
                    let uu____2738 =
                      let uu____2740 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2740
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2736 uu____2738 msg))
  
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____2793  ->
                let uu____2794 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2794)
             (fun uu____2799  ->
                let e1 =
                  let uu___390_2801 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___390_2801.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___390_2801.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___390_2801.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___390_2801.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___390_2801.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___390_2801.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___390_2801.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___390_2801.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___390_2801.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___390_2801.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___390_2801.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___390_2801.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___390_2801.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___390_2801.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___390_2801.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___390_2801.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___390_2801.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___390_2801.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___390_2801.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___390_2801.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___390_2801.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___390_2801.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___390_2801.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___390_2801.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___390_2801.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___390_2801.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___390_2801.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___390_2801.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___390_2801.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___390_2801.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___390_2801.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___390_2801.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___390_2801.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___390_2801.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___390_2801.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___390_2801.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___390_2801.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___390_2801.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___390_2801.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___390_2801.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___390_2801.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___390_2801.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___392_2816  ->
                     match () with
                     | () ->
                         let uu____2825 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2825 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2863,msg) ->
                    let uu____2867 = tts e1 t  in
                    let uu____2869 =
                      let uu____2871 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2871
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2867 uu____2869 msg
                | FStar_Errors.Error (uu____2881,msg,uu____2883) ->
                    let uu____2886 = tts e1 t  in
                    let uu____2888 =
                      let uu____2890 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2890
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2886 uu____2888 msg))
  
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Reflection_Data.typ *
        FStar_TypeChecker_Env.guard_t) tac)
  =
  fun e  ->
    fun t  ->
      bind get
        (fun ps  ->
           mlog
             (fun uu____2943  ->
                let uu____2944 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2944)
             (fun uu____2950  ->
                let e1 =
                  let uu___393_2952 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___393_2952.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___393_2952.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___393_2952.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___393_2952.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___393_2952.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___393_2952.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___393_2952.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___393_2952.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___393_2952.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___393_2952.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___393_2952.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___393_2952.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___393_2952.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___393_2952.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___393_2952.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___393_2952.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___393_2952.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___393_2952.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___393_2952.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___393_2952.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___393_2952.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___393_2952.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___393_2952.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___393_2952.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___393_2952.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___393_2952.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___393_2952.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___393_2952.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___393_2952.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___393_2952.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___393_2952.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___393_2952.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___393_2952.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___393_2952.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___393_2952.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___393_2952.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___393_2952.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___393_2952.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___393_2952.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___393_2952.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___393_2952.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___393_2952.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___394_2955 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___394_2955.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___394_2955.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___394_2955.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___394_2955.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___394_2955.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___394_2955.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___394_2955.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___394_2955.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___394_2955.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___394_2955.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___394_2955.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___394_2955.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___394_2955.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___394_2955.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___394_2955.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___394_2955.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___394_2955.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___394_2955.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___394_2955.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___394_2955.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___394_2955.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___394_2955.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___394_2955.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___394_2955.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___394_2955.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___394_2955.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___394_2955.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___394_2955.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___394_2955.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___394_2955.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___394_2955.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___394_2955.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___394_2955.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___394_2955.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___394_2955.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___394_2955.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___394_2955.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___394_2955.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___394_2955.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___394_2955.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___394_2955.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___394_2955.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___396_2970  ->
                     match () with
                     | () ->
                         let uu____2979 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2979 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3017,msg) ->
                    let uu____3021 = tts e2 t  in
                    let uu____3023 =
                      let uu____3025 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3025
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3021 uu____3023 msg
                | FStar_Errors.Error (uu____3035,msg,uu____3037) ->
                    let uu____3040 = tts e2 t  in
                    let uu____3042 =
                      let uu____3044 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3044
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3040 uu____3042 msg))
  
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
  fun uu____3078  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___397_3097 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___397_3097.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___397_3097.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___397_3097.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___397_3097.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___397_3097.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___397_3097.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___397_3097.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___397_3097.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___397_3097.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___397_3097.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___397_3097.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___397_3097.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3122 = get_guard_policy ()  in
      bind uu____3122
        (fun old_pol  ->
           let uu____3128 = set_guard_policy pol  in
           bind uu____3128
             (fun uu____3132  ->
                bind t
                  (fun r  ->
                     let uu____3136 = set_guard_policy old_pol  in
                     bind uu____3136 (fun uu____3140  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3144 = let uu____3149 = cur_goal ()  in trytac uu____3149  in
  bind uu____3144
    (fun uu___360_3156  ->
       match uu___360_3156 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3162 = FStar_Options.peek ()  in ret uu____3162)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3187  ->
             let uu____3188 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3188)
          (fun uu____3193  ->
             let uu____3194 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3194
               (fun uu____3198  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3202 =
                         let uu____3203 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3203.FStar_TypeChecker_Env.guard_f  in
                       match uu____3202 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3207 = istrivial e f  in
                           if uu____3207
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3220 =
                                          let uu____3226 =
                                            let uu____3228 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3228
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3226)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3220);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3234  ->
                                           let uu____3235 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3235)
                                        (fun uu____3240  ->
                                           let uu____3241 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3241
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___398_3249 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___398_3249.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___398_3249.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___398_3249.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___398_3249.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3253  ->
                                           let uu____3254 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3254)
                                        (fun uu____3259  ->
                                           let uu____3260 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3260
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___399_3268 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___399_3268.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___399_3268.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___399_3268.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___399_3268.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3272  ->
                                           let uu____3273 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3273)
                                        (fun uu____3277  ->
                                           try
                                             (fun uu___401_3282  ->
                                                match () with
                                                | () ->
                                                    let uu____3285 =
                                                      let uu____3287 =
                                                        let uu____3289 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3289
                                                         in
                                                      Prims.op_Negation
                                                        uu____3287
                                                       in
                                                    if uu____3285
                                                    then
                                                      mlog
                                                        (fun uu____3296  ->
                                                           let uu____3297 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3297)
                                                        (fun uu____3301  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___400_3306 ->
                                               mlog
                                                 (fun uu____3311  ->
                                                    let uu____3312 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3312)
                                                 (fun uu____3316  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3328 =
      let uu____3331 = cur_goal ()  in
      bind uu____3331
        (fun goal  ->
           let uu____3337 =
             let uu____3346 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3346 t  in
           bind uu____3337
             (fun uu____3357  ->
                match uu____3357 with
                | (uu____3366,typ,uu____3368) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____3328
  
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
            let uu____3408 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3408 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3420  ->
    let uu____3423 = cur_goal ()  in
    bind uu____3423
      (fun goal  ->
         let uu____3429 =
           let uu____3431 = FStar_Tactics_Types.goal_env goal  in
           let uu____3432 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3431 uu____3432  in
         if uu____3429
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3438 =
              let uu____3440 = FStar_Tactics_Types.goal_env goal  in
              let uu____3441 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3440 uu____3441  in
            fail1 "Not a trivial goal: %s" uu____3438))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3492 =
               try
                 (fun uu___406_3515  ->
                    match () with
                    | () ->
                        let uu____3526 =
                          let uu____3535 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3535
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3526) ()
               with | uu___405_3546 -> fail "divide: not enough goals"  in
             bind uu____3492
               (fun uu____3583  ->
                  match uu____3583 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___402_3609 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___402_3609.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___402_3609.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___402_3609.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___402_3609.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___402_3609.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___402_3609.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___402_3609.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___402_3609.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___402_3609.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___402_3609.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___402_3609.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3610 = set lp  in
                      bind uu____3610
                        (fun uu____3618  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___403_3634 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___403_3634.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___403_3634.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___403_3634.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___403_3634.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___403_3634.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___403_3634.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___403_3634.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___403_3634.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___403_3634.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___403_3634.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___403_3634.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3635 = set rp  in
                                     bind uu____3635
                                       (fun uu____3643  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___404_3659 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___404_3659.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___404_3659.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3660 = set p'
                                                       in
                                                    bind uu____3660
                                                      (fun uu____3668  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3674 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3696 = divide FStar_BigInt.one f idtac  in
    bind uu____3696
      (fun uu____3709  -> match uu____3709 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3747::uu____3748 ->
             let uu____3751 =
               let uu____3760 = map tau  in
               divide FStar_BigInt.one tau uu____3760  in
             bind uu____3751
               (fun uu____3778  ->
                  match uu____3778 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3820 =
        bind t1
          (fun uu____3825  ->
             let uu____3826 = map t2  in
             bind uu____3826 (fun uu____3834  -> ret ()))
         in
      focus uu____3820
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3844  ->
    let uu____3847 =
      let uu____3850 = cur_goal ()  in
      bind uu____3850
        (fun goal  ->
           let uu____3859 =
             let uu____3866 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3866  in
           match uu____3859 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3875 =
                 let uu____3877 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3877  in
               if uu____3875
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3886 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3886 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3900 = new_uvar "intro" env' typ'  in
                  bind uu____3900
                    (fun uu____3917  ->
                       match uu____3917 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3941 = set_solution goal sol  in
                           bind uu____3941
                             (fun uu____3947  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3949 =
                                  let uu____3952 = bnorm_goal g  in
                                  replace_cur uu____3952  in
                                bind uu____3949 (fun uu____3954  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3959 =
                 let uu____3961 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3962 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3961 uu____3962  in
               fail1 "goal is not an arrow (%s)" uu____3959)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3847
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____3980  ->
    let uu____3987 = cur_goal ()  in
    bind uu____3987
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4006 =
            let uu____4013 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4013  in
          match uu____4006 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4026 =
                let uu____4028 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4028  in
              if uu____4026
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4045 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4045
                    in
                 let bs =
                   let uu____4056 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4056; b]  in
                 let env' =
                   let uu____4082 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4082 bs  in
                 let uu____4083 =
                   let uu____4090 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____4090  in
                 bind uu____4083
                   (fun uu____4110  ->
                      match uu____4110 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4124 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4127 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4124
                              FStar_Parser_Const.effect_Tot_lid uu____4127 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4145 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4145 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4167 =
                                   let uu____4168 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4168.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4167
                                  in
                               let uu____4184 = set_solution goal tm  in
                               bind uu____4184
                                 (fun uu____4193  ->
                                    let uu____4194 =
                                      let uu____4197 =
                                        bnorm_goal
                                          (let uu___407_4200 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___407_4200.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___407_4200.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___407_4200.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___407_4200.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4197  in
                                    bind uu____4194
                                      (fun uu____4207  ->
                                         let uu____4208 =
                                           let uu____4213 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4213, b)  in
                                         ret uu____4208)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4222 =
                let uu____4224 = FStar_Tactics_Types.goal_env goal  in
                let uu____4225 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4224 uu____4225  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4222))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4245 = cur_goal ()  in
    bind uu____4245
      (fun goal  ->
         mlog
           (fun uu____4252  ->
              let uu____4253 =
                let uu____4255 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4255  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4253)
           (fun uu____4261  ->
              let steps =
                let uu____4265 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4265
                 in
              let t =
                let uu____4269 = FStar_Tactics_Types.goal_env goal  in
                let uu____4270 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4269 uu____4270  in
              let uu____4271 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4271))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4296 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4304 -> g.FStar_Tactics_Types.opts
                 | uu____4307 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4312  ->
                    let uu____4313 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4313)
                 (fun uu____4318  ->
                    let uu____4319 = __tc_lax e t  in
                    bind uu____4319
                      (fun uu____4340  ->
                         match uu____4340 with
                         | (t1,uu____4350,uu____4351) ->
                             let steps =
                               let uu____4355 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4355
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4361  ->
                                  let uu____4362 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4362)
                               (fun uu____4366  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4296
  
let (refine_intro : unit -> unit tac) =
  fun uu____4379  ->
    let uu____4382 =
      let uu____4385 = cur_goal ()  in
      bind uu____4385
        (fun g  ->
           let uu____4392 =
             let uu____4403 = FStar_Tactics_Types.goal_env g  in
             let uu____4404 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4403 uu____4404
              in
           match uu____4392 with
           | (uu____4407,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4433 =
                 let uu____4438 =
                   let uu____4443 =
                     let uu____4444 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4444]  in
                   FStar_Syntax_Subst.open_term uu____4443 phi  in
                 match uu____4438 with
                 | (bvs,phi1) ->
                     let uu____4469 =
                       let uu____4470 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4470  in
                     (uu____4469, phi1)
                  in
               (match uu____4433 with
                | (bv1,phi1) ->
                    let uu____4489 =
                      let uu____4492 = FStar_Tactics_Types.goal_env g  in
                      let uu____4493 =
                        let uu____4494 =
                          let uu____4497 =
                            let uu____4498 =
                              let uu____4505 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4505)  in
                            FStar_Syntax_Syntax.NT uu____4498  in
                          [uu____4497]  in
                        FStar_Syntax_Subst.subst uu____4494 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4492
                        uu____4493 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4489
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4514  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4382
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4537 = cur_goal ()  in
      bind uu____4537
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4546 = FStar_Tactics_Types.goal_env goal  in
               let uu____4547 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4546 uu____4547
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4550 = __tc env t  in
           bind uu____4550
             (fun uu____4569  ->
                match uu____4569 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4584  ->
                         let uu____4585 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4587 =
                           let uu____4589 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4589
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4585 uu____4587)
                      (fun uu____4593  ->
                         let uu____4594 =
                           let uu____4597 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4597 guard  in
                         bind uu____4594
                           (fun uu____4600  ->
                              mlog
                                (fun uu____4604  ->
                                   let uu____4605 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4607 =
                                     let uu____4609 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4609
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4605 uu____4607)
                                (fun uu____4613  ->
                                   let uu____4614 =
                                     let uu____4618 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4619 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4618 typ uu____4619  in
                                   bind uu____4614
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4629 =
                                             let uu____4631 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4631 t1  in
                                           let uu____4632 =
                                             let uu____4634 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4634 typ  in
                                           let uu____4635 =
                                             let uu____4637 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4638 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4637 uu____4638  in
                                           let uu____4639 =
                                             let uu____4641 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4642 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4641 uu____4642  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4629 uu____4632 uu____4635
                                             uu____4639)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____4668 =
          mlog
            (fun uu____4673  ->
               let uu____4674 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____4674)
            (fun uu____4679  ->
               let uu____4680 =
                 let uu____4687 = __exact_now set_expected_typ1 tm  in
                 catch uu____4687  in
               bind uu____4680
                 (fun uu___362_4696  ->
                    match uu___362_4696 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4707  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4711  ->
                             let uu____4712 =
                               let uu____4719 =
                                 let uu____4722 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4722
                                   (fun uu____4727  ->
                                      let uu____4728 = refine_intro ()  in
                                      bind uu____4728
                                        (fun uu____4732  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4719  in
                             bind uu____4712
                               (fun uu___361_4739  ->
                                  match uu___361_4739 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4748  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4751  -> ret ())
                                  | FStar_Util.Inl uu____4752 ->
                                      mlog
                                        (fun uu____4754  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4757  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____4668
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4809 = f x  in
          bind uu____4809
            (fun y  ->
               let uu____4817 = mapM f xs  in
               bind uu____4817 (fun ys  -> ret (y :: ys)))
  
let rec (__try_match_by_application :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
    FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
            FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  =
  fun acc  ->
    fun e  ->
      fun ty1  ->
        fun ty2  ->
          let uu____4889 = do_unify e ty1 ty2  in
          bind uu____4889
            (fun uu___363_4903  ->
               if uu___363_4903
               then ret acc
               else
                 (let uu____4923 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4923 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4944 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4946 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4944
                        uu____4946
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4963 =
                        let uu____4965 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4965  in
                      if uu____4963
                      then fail "Codomain is effectful"
                      else
                        (let uu____4989 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4989
                           (fun uu____5016  ->
                              match uu____5016 with
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
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
          FStar_Syntax_Syntax.ctx_uvar) Prims.list tac)
  = fun e  -> fun ty1  -> fun ty2  -> __try_match_by_application [] e ty1 ty2 
let (t_apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____5106 =
        mlog
          (fun uu____5111  ->
             let uu____5112 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5112)
          (fun uu____5117  ->
             let uu____5118 = cur_goal ()  in
             bind uu____5118
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5126 = __tc e tm  in
                  bind uu____5126
                    (fun uu____5147  ->
                       match uu____5147 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5160 =
                             let uu____5171 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5171  in
                           bind uu____5160
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____5209)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____5213 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5236  ->
                                       fun w  ->
                                         match uu____5236 with
                                         | (uvt,q,uu____5254) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5286 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5303  ->
                                       fun s  ->
                                         match uu____5303 with
                                         | (uu____5315,uu____5316,uv) ->
                                             let uu____5318 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5318) uvs uu____5286
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5328 = solve' goal w  in
                                bind uu____5328
                                  (fun uu____5333  ->
                                     let uu____5334 =
                                       mapM
                                         (fun uu____5351  ->
                                            match uu____5351 with
                                            | (uvt,q,uv) ->
                                                let uu____5363 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5363 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5368 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5369 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5369
                                                     then ret ()
                                                     else
                                                       (let uu____5376 =
                                                          let uu____5379 =
                                                            bnorm_goal
                                                              (let uu___408_5382
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___408_5382.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___408_5382.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___408_5382.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5379]  in
                                                        add_goals uu____5376)))
                                         uvs
                                        in
                                     bind uu____5334
                                       (fun uu____5387  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5106
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5415 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5415
    then
      let uu____5424 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5439 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5492 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5424 with
      | (pre,post) ->
          let post1 =
            let uu____5525 =
              let uu____5536 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5536]  in
            FStar_Syntax_Util.mk_app post uu____5525  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5567 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5567
       then
         let uu____5576 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5576
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let rec fold_left :
  'a 'b . ('a -> 'b -> 'b tac) -> 'b -> 'a Prims.list -> 'b tac =
  fun f  ->
    fun e  ->
      fun xs  ->
        match xs with
        | [] -> ret e
        | x::xs1 ->
            let uu____5655 = f x e  in
            bind uu____5655 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____5670 =
      let uu____5673 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____5680  ->
                  let uu____5681 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____5681)
               (fun uu____5687  ->
                  let is_unit_t t =
                    let uu____5695 =
                      let uu____5696 = FStar_Syntax_Subst.compress t  in
                      uu____5696.FStar_Syntax_Syntax.n  in
                    match uu____5695 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____5702 -> false  in
                  let uu____5704 = cur_goal ()  in
                  bind uu____5704
                    (fun goal  ->
                       let uu____5710 =
                         let uu____5719 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____5719 tm  in
                       bind uu____5710
                         (fun uu____5734  ->
                            match uu____5734 with
                            | (tm1,t,guard) ->
                                let uu____5746 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____5746 with
                                 | (bs,comp) ->
                                     let uu____5779 = lemma_or_sq comp  in
                                     (match uu____5779 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____5799 =
                                            fold_left
                                              (fun uu____5861  ->
                                                 fun uu____5862  ->
                                                   match (uu____5861,
                                                           uu____5862)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____6013 =
                                                         is_unit_t b_t  in
                                                       if uu____6013
                                                       then
                                                         FStar_All.pipe_left
                                                           ret
                                                           (((FStar_Syntax_Util.exp_unit,
                                                               aq) :: uvs),
                                                             imps,
                                                             ((FStar_Syntax_Syntax.NT
                                                                 (b,
                                                                   FStar_Syntax_Util.exp_unit))
                                                             :: subst1))
                                                       else
                                                         (let uu____6136 =
                                                            let uu____6143 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6143 b_t
                                                             in
                                                          bind uu____6136
                                                            (fun uu____6174 
                                                               ->
                                                               match uu____6174
                                                               with
                                                               | (t1,u) ->
                                                                   FStar_All.pipe_left
                                                                    ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst1)))))
                                              ([], [], []) bs
                                             in
                                          bind uu____5799
                                            (fun uu____6360  ->
                                               match uu____6360 with
                                               | (uvs,implicits,subst1) ->
                                                   let implicits1 =
                                                     FStar_List.rev implicits
                                                      in
                                                   let uvs1 =
                                                     FStar_List.rev uvs  in
                                                   let pre1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 pre
                                                      in
                                                   let post1 =
                                                     FStar_Syntax_Subst.subst
                                                       subst1 post
                                                      in
                                                   let uu____6448 =
                                                     let uu____6452 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6453 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6454 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6452
                                                       uu____6453 uu____6454
                                                      in
                                                   bind uu____6448
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6465 =
                                                            let uu____6467 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6467
                                                              tm1
                                                             in
                                                          let uu____6468 =
                                                            let uu____6470 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6471 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____6470
                                                              uu____6471
                                                             in
                                                          let uu____6472 =
                                                            let uu____6474 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6475 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6474
                                                              uu____6475
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6465
                                                            uu____6468
                                                            uu____6472
                                                        else
                                                          (let uu____6479 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6479
                                                             (fun uu____6487 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____6513
                                                                    =
                                                                    let uu____6516
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6516
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6513
                                                                     in
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun u  ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars
                                                                   in
                                                                let appears
                                                                  uv goals =
                                                                  FStar_List.existsML
                                                                    (
                                                                    fun g' 
                                                                    ->
                                                                    let uu____6552
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6552)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____6569
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____6569
                                                                  with
                                                                  | (hd1,uu____6588)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6615)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6632
                                                                    -> false)
                                                                   in
                                                                let uu____6634
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    implicits1
                                                                    (
                                                                    mapM
                                                                    (fun imp 
                                                                    ->
                                                                    let t1 =
                                                                    FStar_Util.now
                                                                    ()  in
                                                                    let uu____6677
                                                                    = imp  in
                                                                    match uu____6677
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____6688
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____6688
                                                                    with
                                                                    | 
                                                                    (hd1,uu____6710)
                                                                    ->
                                                                    let uu____6735
                                                                    =
                                                                    let uu____6736
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____6736.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____6735
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____6744)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___409_6764
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___409_6764.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___409_6764.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___409_6764.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___409_6764.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____6767
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____6773
                                                                     ->
                                                                    let uu____6774
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____6776
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____6774
                                                                    uu____6776)
                                                                    (fun
                                                                    uu____6783
                                                                     ->
                                                                    let env =
                                                                    let uu___410_6785
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___410_6785.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____6788
                                                                    =
                                                                    let uu____6791
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____6795
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____6797
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____6795
                                                                    uu____6797
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____6803
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____6791
                                                                    uu____6803
                                                                    g_typ  in
                                                                    bind
                                                                    uu____6788
                                                                    (fun
                                                                    uu____6807
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____6634
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
                                                                    let uu____6871
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____6871
                                                                    then
                                                                    let uu____6876
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____6876
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
                                                                    let uu____6891
                                                                    =
                                                                    let uu____6893
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____6893
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____6891)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____6894
                                                                    =
                                                                    let uu____6897
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____6897
                                                                    guard  in
                                                                    bind
                                                                    uu____6894
                                                                    (fun
                                                                    uu____6901
                                                                     ->
                                                                    let uu____6902
                                                                    =
                                                                    let uu____6905
                                                                    =
                                                                    let uu____6907
                                                                    =
                                                                    let uu____6909
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6910
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____6909
                                                                    uu____6910
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____6907
                                                                     in
                                                                    if
                                                                    uu____6905
                                                                    then
                                                                    let uu____6914
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____6914
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____6902
                                                                    (fun
                                                                    uu____6919
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____5673  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____5670
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____6943 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____6943 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____6953::(e1,uu____6955)::(e2,uu____6957)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____7018 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7043 = destruct_eq' typ  in
    match uu____7043 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7073 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7073 with
         | FStar_Pervasives_Native.Some typ1 -> destruct_eq' typ1
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar  ->
    fun e  ->
      let rec aux e1 =
        let uu____7142 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7142 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7200 = aux e'  in
               FStar_Util.map_opt uu____7200
                 (fun uu____7231  ->
                    match uu____7231 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7257 = aux e  in
      FStar_Util.map_opt uu____7257
        (fun uu____7288  ->
           match uu____7288 with
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
          let uu____7362 =
            let uu____7373 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____7373  in
          FStar_Util.map_opt uu____7362
            (fun uu____7391  ->
               match uu____7391 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___411_7413 = bv  in
                     let uu____7414 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___411_7413.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___411_7413.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7414
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___412_7422 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7423 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7432 =
                       let uu____7435 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7435  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___412_7422.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7423;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7432;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___412_7422.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___412_7422.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___412_7422.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___412_7422.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___413_7436 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___413_7436.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___413_7436.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___413_7436.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___413_7436.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7447 =
      let uu____7450 = cur_goal ()  in
      bind uu____7450
        (fun goal  ->
           let uu____7458 = h  in
           match uu____7458 with
           | (bv,uu____7462) ->
               mlog
                 (fun uu____7470  ->
                    let uu____7471 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____7473 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____7471
                      uu____7473)
                 (fun uu____7478  ->
                    let uu____7479 =
                      let uu____7490 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____7490  in
                    match uu____7479 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____7517 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____7517 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____7532 =
                               let uu____7533 = FStar_Syntax_Subst.compress x
                                  in
                               uu____7533.FStar_Syntax_Syntax.n  in
                             (match uu____7532 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___414_7550 = bv2  in
                                    let uu____7551 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___414_7550.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___414_7550.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7551
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___415_7559 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____7560 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____7569 =
                                      let uu____7572 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____7572
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___415_7559.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____7560;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____7569;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___415_7559.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___415_7559.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___415_7559.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___415_7559.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___416_7575 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___416_7575.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___416_7575.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___416_7575.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___416_7575.FStar_Tactics_Types.label)
                                     })
                              | uu____7576 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____7578 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7447
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____7608 =
        let uu____7611 = cur_goal ()  in
        bind uu____7611
          (fun goal  ->
             let uu____7622 = b  in
             match uu____7622 with
             | (bv,uu____7626) ->
                 let bv' =
                   let uu____7632 =
                     let uu___417_7633 = bv  in
                     let uu____7634 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____7634;
                       FStar_Syntax_Syntax.index =
                         (uu___417_7633.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___417_7633.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____7632  in
                 let s1 =
                   let uu____7639 =
                     let uu____7640 =
                       let uu____7647 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____7647)  in
                     FStar_Syntax_Syntax.NT uu____7640  in
                   [uu____7639]  in
                 let uu____7652 = subst_goal bv bv' s1 goal  in
                 (match uu____7652 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____7608
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____7674 =
      let uu____7677 = cur_goal ()  in
      bind uu____7677
        (fun goal  ->
           let uu____7686 = b  in
           match uu____7686 with
           | (bv,uu____7690) ->
               let uu____7695 =
                 let uu____7706 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____7706  in
               (match uu____7695 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____7733 = FStar_Syntax_Util.type_u ()  in
                    (match uu____7733 with
                     | (ty,u) ->
                         let uu____7742 = new_uvar "binder_retype" e0 ty  in
                         bind uu____7742
                           (fun uu____7761  ->
                              match uu____7761 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___418_7771 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___418_7771.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___418_7771.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____7775 =
                                      let uu____7776 =
                                        let uu____7783 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____7783)  in
                                      FStar_Syntax_Syntax.NT uu____7776  in
                                    [uu____7775]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___419_7795 = b1  in
                                         let uu____7796 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___419_7795.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___419_7795.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____7796
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____7803  ->
                                       let new_goal =
                                         let uu____7805 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____7806 =
                                           let uu____7807 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____7807
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7805 uu____7806
                                          in
                                       let uu____7808 = add_goals [new_goal]
                                          in
                                       bind uu____7808
                                         (fun uu____7813  ->
                                            let uu____7814 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____7814
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____7674
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____7840 =
        let uu____7843 = cur_goal ()  in
        bind uu____7843
          (fun goal  ->
             let uu____7852 = b  in
             match uu____7852 with
             | (bv,uu____7856) ->
                 let uu____7861 =
                   let uu____7872 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____7872  in
                 (match uu____7861 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____7902 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____7902
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___420_7907 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___420_7907.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___420_7907.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____7909 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____7909))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____7840
  
let (revert : unit -> unit tac) =
  fun uu____7922  ->
    let uu____7925 = cur_goal ()  in
    bind uu____7925
      (fun goal  ->
         let uu____7931 =
           let uu____7938 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7938  in
         match uu____7931 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____7955 =
                 let uu____7958 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____7958  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____7955
                in
             let uu____7973 = new_uvar "revert" env' typ'  in
             bind uu____7973
               (fun uu____7989  ->
                  match uu____7989 with
                  | (r,u_r) ->
                      let uu____7998 =
                        let uu____8001 =
                          let uu____8002 =
                            let uu____8003 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8003.FStar_Syntax_Syntax.pos  in
                          let uu____8006 =
                            let uu____8011 =
                              let uu____8012 =
                                let uu____8021 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8021  in
                              [uu____8012]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8011  in
                          uu____8006 FStar_Pervasives_Native.None uu____8002
                           in
                        set_solution goal uu____8001  in
                      bind uu____7998
                        (fun uu____8042  ->
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
      let uu____8056 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8056
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8072 = cur_goal ()  in
    bind uu____8072
      (fun goal  ->
         mlog
           (fun uu____8080  ->
              let uu____8081 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8083 =
                let uu____8085 =
                  let uu____8087 =
                    let uu____8096 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8096  in
                  FStar_All.pipe_right uu____8087 FStar_List.length  in
                FStar_All.pipe_right uu____8085 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8081 uu____8083)
           (fun uu____8117  ->
              let uu____8118 =
                let uu____8129 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8129  in
              match uu____8118 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8174 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8174
                        then
                          let uu____8179 =
                            let uu____8181 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8181
                             in
                          fail uu____8179
                        else check1 bvs2
                     in
                  let uu____8186 =
                    let uu____8188 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8188  in
                  if uu____8186
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8195 = check1 bvs  in
                     bind uu____8195
                       (fun uu____8201  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8203 =
                            let uu____8210 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8210  in
                          bind uu____8203
                            (fun uu____8220  ->
                               match uu____8220 with
                               | (ut,uvar_ut) ->
                                   let uu____8229 = set_solution goal ut  in
                                   bind uu____8229
                                     (fun uu____8234  ->
                                        let uu____8235 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8235))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8243  ->
    let uu____8246 = cur_goal ()  in
    bind uu____8246
      (fun goal  ->
         let uu____8252 =
           let uu____8259 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8259  in
         match uu____8252 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8268) ->
             let uu____8273 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8273)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8286 = cur_goal ()  in
    bind uu____8286
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8296 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8296  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8299  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____8312 = cur_goal ()  in
    bind uu____8312
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8322 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8322  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8325  -> add_goals [g']))
  
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
            let uu____8366 = FStar_Syntax_Subst.compress t  in
            uu____8366.FStar_Syntax_Syntax.n  in
          let uu____8369 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___424_8376 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___424_8376.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___424_8376.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____8369
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____8393 =
                   let uu____8394 = FStar_Syntax_Subst.compress t1  in
                   uu____8394.FStar_Syntax_Syntax.n  in
                 match uu____8393 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8425 = ff hd1  in
                     bind uu____8425
                       (fun hd2  ->
                          let fa uu____8451 =
                            match uu____8451 with
                            | (a,q) ->
                                let uu____8472 = ff a  in
                                bind uu____8472 (fun a1  -> ret (a1, q))
                             in
                          let uu____8491 = mapM fa args  in
                          bind uu____8491
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____8573 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____8573 with
                      | (bs1,t') ->
                          let uu____8582 =
                            let uu____8585 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____8585 t'  in
                          bind uu____8582
                            (fun t''  ->
                               let uu____8589 =
                                 let uu____8590 =
                                   let uu____8609 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____8618 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____8609, uu____8618, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____8590  in
                               ret uu____8589))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____8693 = ff hd1  in
                     bind uu____8693
                       (fun hd2  ->
                          let ffb br =
                            let uu____8708 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____8708 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____8740 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____8740  in
                                let uu____8741 = ff1 e  in
                                bind uu____8741
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____8756 = mapM ffb brs  in
                          bind uu____8756
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____8800;
                          FStar_Syntax_Syntax.lbtyp = uu____8801;
                          FStar_Syntax_Syntax.lbeff = uu____8802;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____8804;
                          FStar_Syntax_Syntax.lbpos = uu____8805;_}::[]),e)
                     ->
                     let lb =
                       let uu____8833 =
                         let uu____8834 = FStar_Syntax_Subst.compress t1  in
                         uu____8834.FStar_Syntax_Syntax.n  in
                       match uu____8833 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____8838) -> lb
                       | uu____8854 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____8864 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8864
                         (fun def1  ->
                            ret
                              (let uu___421_8870 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___421_8870.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___421_8870.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___421_8870.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___421_8870.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___421_8870.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___421_8870.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8871 = fflb lb  in
                     bind uu____8871
                       (fun lb1  ->
                          let uu____8881 =
                            let uu____8886 =
                              let uu____8887 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____8887]  in
                            FStar_Syntax_Subst.open_term uu____8886 e  in
                          match uu____8881 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____8917 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____8917  in
                              let uu____8918 = ff1 e1  in
                              bind uu____8918
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____8965 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8965
                         (fun def  ->
                            ret
                              (let uu___422_8971 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___422_8971.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___422_8971.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___422_8971.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___422_8971.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___422_8971.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___422_8971.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8972 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____8972 with
                      | (lbs1,e1) ->
                          let uu____8987 = mapM fflb lbs1  in
                          bind uu____8987
                            (fun lbs2  ->
                               let uu____8999 = ff e1  in
                               bind uu____8999
                                 (fun e2  ->
                                    let uu____9007 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9007 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9078 = ff t2  in
                     bind uu____9078
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9109 = ff t2  in
                     bind uu____9109
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9116 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___423_9123 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___423_9123.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___423_9123.FStar_Syntax_Syntax.vars)
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
              let uu____9170 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___425_9179 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___425_9179.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___425_9179.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___425_9179.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___425_9179.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___425_9179.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___425_9179.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___425_9179.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___425_9179.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___425_9179.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___425_9179.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___425_9179.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___425_9179.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___425_9179.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___425_9179.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___425_9179.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___425_9179.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___425_9179.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___425_9179.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___425_9179.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___425_9179.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___425_9179.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___425_9179.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___425_9179.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___425_9179.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___425_9179.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___425_9179.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___425_9179.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___425_9179.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___425_9179.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___425_9179.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___425_9179.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___425_9179.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___425_9179.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___425_9179.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___425_9179.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___425_9179.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___425_9179.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___425_9179.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___425_9179.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___425_9179.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___425_9179.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___425_9179.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9170 with
              | (t1,lcomp,g) ->
                  let uu____9186 =
                    (let uu____9190 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9190) ||
                      (let uu____9193 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9193)
                     in
                  if uu____9186
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9204 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9204
                         (fun uu____9221  ->
                            match uu____9221 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9234  ->
                                      let uu____9235 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9237 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9235 uu____9237);
                                 (let uu____9240 =
                                    let uu____9243 =
                                      let uu____9244 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9244 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9243
                                      opts label1
                                     in
                                  bind uu____9240
                                    (fun uu____9248  ->
                                       let uu____9249 =
                                         bind tau
                                           (fun uu____9255  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9261  ->
                                                   let uu____9262 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9264 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9262 uu____9264);
                                              ret ut1)
                                          in
                                       focus uu____9249))))
                        in
                     let uu____9267 = catch rewrite_eq  in
                     bind uu____9267
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
type 'a ctrl_tac = ('a * ctrl) tac
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
          let uu____9485 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____9485
            (fun t1  ->
               let uu____9493 =
                 f env
                   (let uu___428_9502 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___428_9502.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___428_9502.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____9493
                 (fun uu____9518  ->
                    match uu____9518 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____9541 =
                               let uu____9542 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____9542.FStar_Syntax_Syntax.n  in
                             match uu____9541 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____9579 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____9579
                                   (fun uu____9604  ->
                                      match uu____9604 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____9620 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____9620
                                            (fun uu____9647  ->
                                               match uu____9647 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___426_9677 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___426_9677.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___426_9677.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____9719 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____9719 with
                                  | (bs1,t') ->
                                      let uu____9734 =
                                        let uu____9741 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____9741 ctrl1 t'
                                         in
                                      bind uu____9734
                                        (fun uu____9759  ->
                                           match uu____9759 with
                                           | (t'',ctrl2) ->
                                               let uu____9774 =
                                                 let uu____9781 =
                                                   let uu___427_9784 = t4  in
                                                   let uu____9787 =
                                                     let uu____9788 =
                                                       let uu____9807 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____9816 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____9807,
                                                         uu____9816, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____9788
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____9787;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___427_9784.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___427_9784.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____9781, ctrl2)  in
                                               ret uu____9774))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____9869 -> ret (t3, ctrl1))))

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
              let uu____9916 = ctrl_tac_fold f env ctrl t  in
              bind uu____9916
                (fun uu____9940  ->
                   match uu____9940 with
                   | (t1,ctrl1) ->
                       let uu____9955 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____9955
                         (fun uu____9982  ->
                            match uu____9982 with
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
                let uu____10076 =
                  let uu____10084 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10084
                    (fun uu____10095  ->
                       let uu____10096 = ctrl t1  in
                       bind uu____10096
                         (fun res  ->
                            let uu____10123 = trivial ()  in
                            bind uu____10123 (fun uu____10132  -> ret res)))
                   in
                bind uu____10076
                  (fun uu____10150  ->
                     match uu____10150 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10179 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___429_10188 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___429_10188.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___429_10188.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___429_10188.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___429_10188.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___429_10188.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___429_10188.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___429_10188.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___429_10188.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___429_10188.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___429_10188.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___429_10188.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___429_10188.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___429_10188.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___429_10188.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___429_10188.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___429_10188.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___429_10188.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___429_10188.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___429_10188.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___429_10188.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___429_10188.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___429_10188.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___429_10188.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___429_10188.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___429_10188.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___429_10188.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___429_10188.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___429_10188.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___429_10188.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___429_10188.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___429_10188.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___429_10188.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___429_10188.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___429_10188.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___429_10188.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___429_10188.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___429_10188.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___429_10188.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___429_10188.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___429_10188.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___429_10188.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___429_10188.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10179 with
                            | (t2,lcomp,g) ->
                                let uu____10199 =
                                  (let uu____10203 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10203) ||
                                    (let uu____10206 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10206)
                                   in
                                if uu____10199
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10222 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10222
                                     (fun uu____10243  ->
                                        match uu____10243 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10260  ->
                                                  let uu____10261 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10263 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10261 uu____10263);
                                             (let uu____10266 =
                                                let uu____10269 =
                                                  let uu____10270 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10270 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10269 opts label1
                                                 in
                                              bind uu____10266
                                                (fun uu____10278  ->
                                                   let uu____10279 =
                                                     bind rewriter
                                                       (fun uu____10293  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10299 
                                                               ->
                                                               let uu____10300
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10302
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10300
                                                                 uu____10302);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10279)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____10348 =
        bind get
          (fun ps  ->
             let uu____10358 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10358 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10396  ->
                       let uu____10397 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10397);
                  bind dismiss_all
                    (fun uu____10402  ->
                       let uu____10403 =
                         let uu____10410 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10410
                           keepGoing gt1
                          in
                       bind uu____10403
                         (fun uu____10422  ->
                            match uu____10422 with
                            | (gt',uu____10430) ->
                                (log ps
                                   (fun uu____10434  ->
                                      let uu____10435 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10435);
                                 (let uu____10438 = push_goals gs  in
                                  bind uu____10438
                                    (fun uu____10443  ->
                                       let uu____10444 =
                                         let uu____10447 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10447]  in
                                       add_goals uu____10444)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10348
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10472 =
        bind get
          (fun ps  ->
             let uu____10482 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10482 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10520  ->
                       let uu____10521 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____10521);
                  bind dismiss_all
                    (fun uu____10526  ->
                       let uu____10527 =
                         let uu____10530 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10530 gt1
                          in
                       bind uu____10527
                         (fun gt'  ->
                            log ps
                              (fun uu____10538  ->
                                 let uu____10539 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____10539);
                            (let uu____10542 = push_goals gs  in
                             bind uu____10542
                               (fun uu____10547  ->
                                  let uu____10548 =
                                    let uu____10551 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____10551]  in
                                  add_goals uu____10548))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10472
  
let (trefl : unit -> unit tac) =
  fun uu____10564  ->
    let uu____10567 =
      let uu____10570 = cur_goal ()  in
      bind uu____10570
        (fun g  ->
           let uu____10588 =
             let uu____10593 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____10593  in
           match uu____10588 with
           | FStar_Pervasives_Native.Some t ->
               let uu____10601 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____10601 with
                | (hd1,args) ->
                    let uu____10640 =
                      let uu____10653 =
                        let uu____10654 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____10654.FStar_Syntax_Syntax.n  in
                      (uu____10653, args)  in
                    (match uu____10640 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____10668::(l,uu____10670)::(r,uu____10672)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____10719 =
                           let uu____10723 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____10723 l r  in
                         bind uu____10719
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____10734 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10734 l
                                    in
                                 let r1 =
                                   let uu____10736 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10736 r
                                    in
                                 let uu____10737 =
                                   let uu____10741 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____10741 l1 r1  in
                                 bind uu____10737
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____10751 =
                                           let uu____10753 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10753 l1  in
                                         let uu____10754 =
                                           let uu____10756 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10756 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____10751 uu____10754))))
                     | (hd2,uu____10759) ->
                         let uu____10776 =
                           let uu____10778 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____10778 t  in
                         fail1 "trefl: not an equality (%s)" uu____10776))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____10567
  
let (dup : unit -> unit tac) =
  fun uu____10795  ->
    let uu____10798 = cur_goal ()  in
    bind uu____10798
      (fun g  ->
         let uu____10804 =
           let uu____10811 = FStar_Tactics_Types.goal_env g  in
           let uu____10812 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____10811 uu____10812  in
         bind uu____10804
           (fun uu____10822  ->
              match uu____10822 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___430_10832 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___430_10832.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___430_10832.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___430_10832.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___430_10832.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____10835  ->
                       let uu____10836 =
                         let uu____10839 = FStar_Tactics_Types.goal_env g  in
                         let uu____10840 =
                           let uu____10841 =
                             let uu____10842 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____10843 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____10842
                               uu____10843
                              in
                           let uu____10844 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____10845 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____10841 uu____10844 u
                             uu____10845
                            in
                         add_irrelevant_goal "dup equation" uu____10839
                           uu____10840 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____10836
                         (fun uu____10849  ->
                            let uu____10850 = add_goals [g']  in
                            bind uu____10850 (fun uu____10854  -> ret ())))))
  
let rec longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f  ->
    fun l1  ->
      fun l2  ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs,y::ys) ->
              let uu____10980 = f x y  in
              if uu____10980 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11003 -> (acc, l11, l21)  in
        let uu____11018 = aux [] l1 l2  in
        match uu____11018 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11124 = get_phi g1  in
      match uu____11124 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11131 = get_phi g2  in
          (match uu____11131 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11144 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11144 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11175 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11175 phi1  in
                    let t2 =
                      let uu____11185 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11185 phi2  in
                    let uu____11194 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11194
                      (fun uu____11199  ->
                         let uu____11200 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11200
                           (fun uu____11207  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___431_11212 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11213 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___431_11212.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___431_11212.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___431_11212.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___431_11212.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11213;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___431_11212.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___431_11212.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___431_11212.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___431_11212.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___431_11212.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___431_11212.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___431_11212.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___431_11212.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___431_11212.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___431_11212.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___431_11212.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___431_11212.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___431_11212.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___431_11212.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___431_11212.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___431_11212.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___431_11212.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___431_11212.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___431_11212.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___431_11212.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___431_11212.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___431_11212.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___431_11212.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___431_11212.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___431_11212.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___431_11212.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___431_11212.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___431_11212.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___431_11212.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___431_11212.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___431_11212.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___431_11212.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___431_11212.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___431_11212.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___431_11212.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___431_11212.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___431_11212.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11217 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11217
                                (fun goal  ->
                                   mlog
                                     (fun uu____11227  ->
                                        let uu____11228 =
                                          goal_to_string_verbose g1  in
                                        let uu____11230 =
                                          goal_to_string_verbose g2  in
                                        let uu____11232 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11228 uu____11230 uu____11232)
                                     (fun uu____11236  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11244  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11260 =
               set
                 (let uu___432_11265 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___432_11265.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___432_11265.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___432_11265.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___432_11265.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___432_11265.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___432_11265.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___432_11265.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___432_11265.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___432_11265.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___432_11265.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___432_11265.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___432_11265.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11260
               (fun uu____11268  ->
                  let uu____11269 = join_goals g1 g2  in
                  bind uu____11269 (fun g12  -> add_goals [g12]))
         | uu____11274 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____11296 =
      let uu____11303 = cur_goal ()  in
      bind uu____11303
        (fun g  ->
           let uu____11313 =
             let uu____11322 = FStar_Tactics_Types.goal_env g  in
             __tc uu____11322 t  in
           bind uu____11313
             (fun uu____11350  ->
                match uu____11350 with
                | (t1,typ,guard) ->
                    let uu____11366 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____11366 with
                     | (hd1,args) ->
                         let uu____11415 =
                           let uu____11430 =
                             let uu____11431 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____11431.FStar_Syntax_Syntax.n  in
                           (uu____11430, args)  in
                         (match uu____11415 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____11452)::(q,uu____11454)::[]) when
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
                                let uu____11508 =
                                  let uu____11509 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11509
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11508
                                 in
                              let g2 =
                                let uu____11511 =
                                  let uu____11512 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11512
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11511
                                 in
                              bind __dismiss
                                (fun uu____11519  ->
                                   let uu____11520 = add_goals [g1; g2]  in
                                   bind uu____11520
                                     (fun uu____11529  ->
                                        let uu____11530 =
                                          let uu____11535 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____11536 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____11535, uu____11536)  in
                                        ret uu____11530))
                          | uu____11541 ->
                              let uu____11556 =
                                let uu____11558 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____11558 typ  in
                              fail1 "Not a disjunction: %s" uu____11556))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____11296
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11593 =
      let uu____11596 = cur_goal ()  in
      bind uu____11596
        (fun g  ->
           FStar_Options.push ();
           (let uu____11609 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11609);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___433_11616 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___433_11616.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___433_11616.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___433_11616.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___433_11616.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11593
  
let (top_env : unit -> env tac) =
  fun uu____11633  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11648  ->
    let uu____11652 = cur_goal ()  in
    bind uu____11652
      (fun g  ->
         let uu____11659 =
           (FStar_Options.lax ()) ||
             (let uu____11662 = FStar_Tactics_Types.goal_env g  in
              uu____11662.FStar_TypeChecker_Env.lax)
            in
         ret uu____11659)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11679 =
        mlog
          (fun uu____11684  ->
             let uu____11685 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11685)
          (fun uu____11690  ->
             let uu____11691 = cur_goal ()  in
             bind uu____11691
               (fun goal  ->
                  let env =
                    let uu____11699 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11699 ty  in
                  let uu____11700 = __tc_ghost env tm  in
                  bind uu____11700
                    (fun uu____11719  ->
                       match uu____11719 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11733  ->
                                let uu____11734 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11734)
                             (fun uu____11738  ->
                                mlog
                                  (fun uu____11741  ->
                                     let uu____11742 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11742)
                                  (fun uu____11747  ->
                                     let uu____11748 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11748
                                       (fun uu____11753  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11679
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11778 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11784 =
              let uu____11791 =
                let uu____11792 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11792
                 in
              new_uvar "uvar_env.2" env uu____11791  in
            bind uu____11784
              (fun uu____11809  ->
                 match uu____11809 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11778
        (fun typ  ->
           let uu____11821 = new_uvar "uvar_env" env typ  in
           bind uu____11821
             (fun uu____11836  ->
                match uu____11836 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____11855 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____11874 -> g.FStar_Tactics_Types.opts
             | uu____11877 -> FStar_Options.peek ()  in
           let uu____11880 = FStar_Syntax_Util.head_and_args t  in
           match uu____11880 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____11900);
                FStar_Syntax_Syntax.pos = uu____11901;
                FStar_Syntax_Syntax.vars = uu____11902;_},uu____11903)
               ->
               let env1 =
                 let uu___434_11945 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___434_11945.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___434_11945.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___434_11945.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___434_11945.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___434_11945.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___434_11945.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___434_11945.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___434_11945.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___434_11945.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___434_11945.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___434_11945.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___434_11945.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___434_11945.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___434_11945.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___434_11945.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___434_11945.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___434_11945.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___434_11945.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___434_11945.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___434_11945.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___434_11945.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___434_11945.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___434_11945.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___434_11945.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___434_11945.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___434_11945.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___434_11945.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___434_11945.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___434_11945.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___434_11945.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___434_11945.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___434_11945.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___434_11945.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___434_11945.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___434_11945.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___434_11945.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___434_11945.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___434_11945.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___434_11945.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___434_11945.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___434_11945.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___434_11945.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____11949 =
                 let uu____11952 = bnorm_goal g  in [uu____11952]  in
               add_goals uu____11949
           | uu____11953 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____11855
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____12015 = if b then t2 else ret false  in
             bind uu____12015 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12041 = trytac comp  in
      bind uu____12041
        (fun uu___364_12053  ->
           match uu___364_12053 with
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
        let uu____12095 =
          bind get
            (fun ps  ->
               let uu____12103 = __tc e t1  in
               bind uu____12103
                 (fun uu____12124  ->
                    match uu____12124 with
                    | (t11,ty1,g1) ->
                        let uu____12137 = __tc e t2  in
                        bind uu____12137
                          (fun uu____12158  ->
                             match uu____12158 with
                             | (t21,ty2,g2) ->
                                 let uu____12171 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12171
                                   (fun uu____12178  ->
                                      let uu____12179 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12179
                                        (fun uu____12187  ->
                                           let uu____12188 =
                                             do_unify e ty1 ty2  in
                                           let uu____12192 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12188 uu____12192)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12095
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12240  ->
             let uu____12241 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12241
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
        (fun uu____12275  ->
           let uu____12276 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12276)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12287 =
      mlog
        (fun uu____12292  ->
           let uu____12293 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12293)
        (fun uu____12298  ->
           let uu____12299 = cur_goal ()  in
           bind uu____12299
             (fun g  ->
                let uu____12305 =
                  let uu____12314 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12314 ty  in
                bind uu____12305
                  (fun uu____12326  ->
                     match uu____12326 with
                     | (ty1,uu____12336,guard) ->
                         let uu____12338 =
                           let uu____12341 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12341 guard  in
                         bind uu____12338
                           (fun uu____12345  ->
                              let uu____12346 =
                                let uu____12350 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12351 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12350 uu____12351 ty1  in
                              bind uu____12346
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12360 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12360
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12367 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12368 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12367
                                          uu____12368
                                         in
                                      let nty =
                                        let uu____12370 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12370 ty1  in
                                      let uu____12371 =
                                        let uu____12375 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12375 ng nty  in
                                      bind uu____12371
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12384 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12384
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12287
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12458 =
      let uu____12467 = cur_goal ()  in
      bind uu____12467
        (fun g  ->
           let uu____12479 =
             let uu____12488 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12488 s_tm  in
           bind uu____12479
             (fun uu____12506  ->
                match uu____12506 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12524 =
                      let uu____12527 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12527 guard  in
                    bind uu____12524
                      (fun uu____12540  ->
                         let uu____12541 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12541 with
                         | (h,args) ->
                             let uu____12586 =
                               let uu____12593 =
                                 let uu____12594 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12594.FStar_Syntax_Syntax.n  in
                               match uu____12593 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12609;
                                      FStar_Syntax_Syntax.vars = uu____12610;_},us)
                                   -> ret (fv, us)
                               | uu____12620 -> fail "type is not an fv"  in
                             bind uu____12586
                               (fun uu____12641  ->
                                  match uu____12641 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12657 =
                                        let uu____12660 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12660 t_lid
                                         in
                                      (match uu____12657 with
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
                                                  (fun uu____12711  ->
                                                     let uu____12712 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12712 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12727 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12755
                                                                  =
                                                                  let uu____12758
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12758
                                                                    c_lid
                                                                   in
                                                                match uu____12755
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
                                                                    uu____12832
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
                                                                    let uu____12837
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____12837
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____12860
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____12860
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____12903
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____12903
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____12976
                                                                    =
                                                                    let uu____12978
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____12978
                                                                     in
                                                                    failwhen
                                                                    uu____12976
                                                                    "not total?"
                                                                    (fun
                                                                    uu____12997
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
                                                                    uu___365_13014
                                                                    =
                                                                    match uu___365_13014
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____13018)
                                                                    -> true
                                                                    | 
                                                                    uu____13021
                                                                    -> false
                                                                     in
                                                                    let uu____13025
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13025
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
                                                                    uu____13159
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
                                                                    uu____13221
                                                                     ->
                                                                    match uu____13221
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13241),
                                                                    (t,uu____13243))
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
                                                                    uu____13313
                                                                     ->
                                                                    match uu____13313
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13340),
                                                                    (t,uu____13342))
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
                                                                    uu____13401
                                                                     ->
                                                                    match uu____13401
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
                                                                    let uu____13456
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___435_13473
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___435_13473.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13456
                                                                    with
                                                                    | 
                                                                    (uu____13487,uu____13488,uu____13489,pat_t,uu____13491,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13498
                                                                    =
                                                                    let uu____13499
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13499
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13498
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13504
                                                                    =
                                                                    let uu____13513
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13513]
                                                                     in
                                                                    let uu____13532
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13504
                                                                    uu____13532
                                                                     in
                                                                    let nty =
                                                                    let uu____13538
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13538
                                                                     in
                                                                    let uu____13541
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13541
                                                                    (fun
                                                                    uu____13571
                                                                     ->
                                                                    match uu____13571
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
                                                                    let uu____13598
                                                                    =
                                                                    let uu____13609
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13609]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13598
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13645
                                                                    =
                                                                    let uu____13656
                                                                    =
                                                                    let uu____13661
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13661)
                                                                     in
                                                                    (g', br,
                                                                    uu____13656)
                                                                     in
                                                                    ret
                                                                    uu____13645))))))
                                                                    | 
                                                                    uu____13682
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12727
                                                           (fun goal_brs  ->
                                                              let uu____13732
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13732
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
                                                                  let uu____13805
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____13805
                                                                    (
                                                                    fun
                                                                    uu____13816
                                                                     ->
                                                                    let uu____13817
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____13817
                                                                    (fun
                                                                    uu____13827
                                                                     ->
                                                                    ret infos))))
                                            | uu____13834 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12458
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____13883::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____13913 = init xs  in x :: uu____13913
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____13926 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____13935) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____14001 = last args  in
          (match uu____14001 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14031 =
                 let uu____14032 =
                   let uu____14037 =
                     let uu____14038 =
                       let uu____14043 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14043  in
                     uu____14038 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14037, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14032  in
               FStar_All.pipe_left ret uu____14031)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14056,uu____14057) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14110 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14110 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14152 =
                      let uu____14153 =
                        let uu____14158 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14158)  in
                      FStar_Reflection_Data.Tv_Abs uu____14153  in
                    FStar_All.pipe_left ret uu____14152))
      | FStar_Syntax_Syntax.Tm_type uu____14161 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14186 ->
          let uu____14201 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14201 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14232 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14232 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14285 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14298 =
            let uu____14299 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14299  in
          FStar_All.pipe_left ret uu____14298
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14320 =
            let uu____14321 =
              let uu____14326 =
                let uu____14327 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14327  in
              (uu____14326, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14321  in
          FStar_All.pipe_left ret uu____14320
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14367 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14372 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14372 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14425 ->
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
             | FStar_Util.Inr uu____14467 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14471 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14471 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14491 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14497 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14552 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14552
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14573 =
                  let uu____14580 =
                    FStar_List.map
                      (fun uu____14593  ->
                         match uu____14593 with
                         | (p1,uu____14602) -> inspect_pat p1) ps
                     in
                  (fv, uu____14580)  in
                FStar_Reflection_Data.Pat_Cons uu____14573
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
              (fun uu___366_14698  ->
                 match uu___366_14698 with
                 | (pat,uu____14720,t5) ->
                     let uu____14738 = inspect_pat pat  in (uu____14738, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14747 ->
          ((let uu____14749 =
              let uu____14755 =
                let uu____14757 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14759 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14757 uu____14759
                 in
              (FStar_Errors.Warning_CantInspect, uu____14755)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14749);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____13926
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14777 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14777
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14781 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14781
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14785 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14785
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____14792 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____14792
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____14817 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____14817
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____14834 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____14834
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____14853 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____14853
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____14857 =
          let uu____14858 =
            let uu____14865 =
              let uu____14866 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____14866  in
            FStar_Syntax_Syntax.mk uu____14865  in
          uu____14858 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14857
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____14874 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14874
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14885 =
          let uu____14886 =
            let uu____14893 =
              let uu____14894 =
                let uu____14908 =
                  let uu____14911 =
                    let uu____14912 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____14912]  in
                  FStar_Syntax_Subst.close uu____14911 t2  in
                ((false, [lb]), uu____14908)  in
              FStar_Syntax_Syntax.Tm_let uu____14894  in
            FStar_Syntax_Syntax.mk uu____14893  in
          uu____14886 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14885
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14957 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____14957 with
         | (lbs,body) ->
             let uu____14972 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____14972)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____15009 =
                let uu____15010 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____15010  in
              FStar_All.pipe_left wrap uu____15009
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____15017 =
                let uu____15018 =
                  let uu____15032 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15050 = pack_pat p1  in
                         (uu____15050, false)) ps
                     in
                  (fv, uu____15032)  in
                FStar_Syntax_Syntax.Pat_cons uu____15018  in
              FStar_All.pipe_left wrap uu____15017
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
            (fun uu___367_15099  ->
               match uu___367_15099 with
               | (pat,t1) ->
                   let uu____15116 = pack_pat pat  in
                   (uu____15116, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15164 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15164
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15192 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15192
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15238 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15238
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15277 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15277
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15297 =
        bind get
          (fun ps  ->
             let uu____15303 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15303 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15297
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15337 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___436_15344 = ps  in
                 let uu____15345 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___436_15344.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___436_15344.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___436_15344.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___436_15344.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___436_15344.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___436_15344.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___436_15344.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___436_15344.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___436_15344.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___436_15344.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___436_15344.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___436_15344.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15345
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15337
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15372 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15372 with
      | (u,ctx_uvars,g_u) ->
          let uu____15405 = FStar_List.hd ctx_uvars  in
          (match uu____15405 with
           | (ctx_uvar,uu____15419) ->
               let g =
                 let uu____15421 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15421 false
                   ""
                  in
               (g, g_u))
  
let (proofstate_of_goal_ty :
  FStar_Range.range ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Tactics_Types.proofstate * FStar_Syntax_Syntax.term))
  =
  fun rng  ->
    fun env  ->
      fun typ  ->
        let uu____15444 = goal_of_goal_ty env typ  in
        match uu____15444 with
        | (g,g_u) ->
            let ps =
              let uu____15456 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15459 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15456;
                FStar_Tactics_Types.local_state = uu____15459
              }  in
            let uu____15469 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15469)
  