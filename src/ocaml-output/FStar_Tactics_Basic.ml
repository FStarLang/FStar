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
        (try (fun uu___366_169  -> match () with | () -> run t p) ()
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
                 let uu___367_1372 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___367_1372.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___367_1372.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___367_1372.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___367_1372.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___367_1372.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___367_1372.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___367_1372.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___367_1372.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___367_1372.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___367_1372.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___367_1372.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___367_1372.FStar_Tactics_Types.local_state)
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
           (fun uu___369_1518  ->
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
           (let uu___370_1634 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1634.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1634.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_1634.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1634.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1634.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1634.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1634.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1634.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1634.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1634.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1634.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1634.FStar_Tactics_Types.local_state)
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
           (fun uu___372_1675  ->
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
         let uu___373_1756 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___373_1756.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___373_1756.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___373_1756.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___374_1759 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___374_1759.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___374_1759.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___374_1759.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___374_1759.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___374_1759.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___374_1759.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___374_1759.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___374_1759.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___374_1759.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___374_1759.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___374_1759.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___374_1759.FStar_Tactics_Types.local_state)
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
                   bind compress_implicits (fun uu____1816  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___375_1825 = ps  in
         let uu____1826 =
           FStar_List.filter
             (fun g  ->
                let uu____1832 = check_goal_solved g  in
                FStar_Option.isNone uu____1832) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___375_1825.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___375_1825.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___375_1825.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1826;
           FStar_Tactics_Types.smt_goals =
             (uu___375_1825.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___375_1825.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___375_1825.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___375_1825.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___375_1825.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___375_1825.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___375_1825.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___375_1825.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___375_1825.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1850 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1850 with
      | FStar_Pervasives_Native.Some uu____1855 ->
          let uu____1856 =
            let uu____1858 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1858  in
          fail uu____1856
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1879 = FStar_Tactics_Types.goal_env goal  in
      let uu____1880 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1879 solution uu____1880
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1887 =
         let uu___376_1888 = p  in
         let uu____1889 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___376_1888.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___376_1888.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___376_1888.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1889;
           FStar_Tactics_Types.smt_goals =
             (uu___376_1888.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___376_1888.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___376_1888.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___376_1888.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___376_1888.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___376_1888.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___376_1888.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___376_1888.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___376_1888.FStar_Tactics_Types.local_state)
         }  in
       set uu____1887)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1911  ->
           let uu____1912 =
             let uu____1914 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1914  in
           let uu____1915 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1912 uu____1915)
        (fun uu____1920  ->
           let uu____1921 = trysolve goal solution  in
           bind uu____1921
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1933  -> remove_solved_goals)
                else
                  (let uu____1936 =
                     let uu____1938 =
                       let uu____1940 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1940 solution  in
                     let uu____1941 =
                       let uu____1943 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1944 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1943 uu____1944  in
                     let uu____1945 =
                       let uu____1947 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1948 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1947 uu____1948  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1938 uu____1941 uu____1945
                      in
                   fail uu____1936)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1965 = set_solution goal solution  in
      bind uu____1965
        (fun uu____1969  ->
           bind __dismiss (fun uu____1971  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___377_1990 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___377_1990.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___377_1990.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___377_1990.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___377_1990.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___377_1990.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___377_1990.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___377_1990.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___377_1990.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___377_1990.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___377_1990.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___377_1990.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___377_1990.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___378_2009 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___378_2009.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___378_2009.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___378_2009.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___378_2009.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___378_2009.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___378_2009.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___378_2009.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___378_2009.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___378_2009.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___378_2009.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___378_2009.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___378_2009.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2036 = FStar_Options.defensive ()  in
    if uu____2036
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2046 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2046)
         in
      let b2 =
        b1 &&
          (let uu____2050 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2050)
         in
      let rec aux b3 e =
        let uu____2065 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2065 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2085 =
        (let uu____2089 = aux b2 env  in Prims.op_Negation uu____2089) &&
          (let uu____2092 = FStar_ST.op_Bang nwarn  in
           uu____2092 < (Prims.parse_int "5"))
         in
      (if uu____2085
       then
         ((let uu____2118 =
             let uu____2119 = FStar_Tactics_Types.goal_type g  in
             uu____2119.FStar_Syntax_Syntax.pos  in
           let uu____2122 =
             let uu____2128 =
               let uu____2130 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2130
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2128)  in
           FStar_Errors.log_issue uu____2118 uu____2122);
          (let uu____2134 =
             let uu____2136 = FStar_ST.op_Bang nwarn  in
             uu____2136 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____2134))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___379_2205 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___379_2205.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___379_2205.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___379_2205.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___379_2205.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___379_2205.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___379_2205.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___379_2205.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___379_2205.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___379_2205.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___379_2205.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___379_2205.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___379_2205.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___380_2226 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___380_2226.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___380_2226.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___380_2226.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___380_2226.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___380_2226.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___380_2226.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___380_2226.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___380_2226.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___380_2226.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___380_2226.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___380_2226.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___380_2226.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___381_2247 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___381_2247.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___381_2247.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___381_2247.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___381_2247.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___381_2247.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___381_2247.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___381_2247.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___381_2247.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___381_2247.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___381_2247.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___381_2247.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___381_2247.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___382_2268 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___382_2268.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___382_2268.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___382_2268.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___382_2268.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___382_2268.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___382_2268.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___382_2268.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___382_2268.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___382_2268.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___382_2268.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___382_2268.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___382_2268.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2280  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2311 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2311 with
        | (u,ctx_uvar,g_u) ->
            let uu____2349 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2349
              (fun uu____2358  ->
                 let uu____2359 =
                   let uu____2364 =
                     let uu____2365 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2365  in
                   (u, uu____2364)  in
                 ret uu____2359)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2385 = FStar_Syntax_Util.un_squash t  in
    match uu____2385 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2396 =
          let uu____2397 = FStar_Syntax_Subst.compress t'  in
          uu____2397.FStar_Syntax_Syntax.n  in
        (match uu____2396 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2402 -> false)
    | uu____2404 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2417 = FStar_Syntax_Util.un_squash t  in
    match uu____2417 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2428 =
          let uu____2429 = FStar_Syntax_Subst.compress t'  in
          uu____2429.FStar_Syntax_Syntax.n  in
        (match uu____2428 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2434 -> false)
    | uu____2436 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2449  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2461 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2461 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2468 = goal_to_string_verbose hd1  in
                    let uu____2470 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2468 uu____2470);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2483 =
      bind get
        (fun ps  ->
           let uu____2489 = cur_goal ()  in
           bind uu____2489
             (fun g  ->
                (let uu____2496 =
                   let uu____2497 = FStar_Tactics_Types.goal_type g  in
                   uu____2497.FStar_Syntax_Syntax.pos  in
                 let uu____2500 =
                   let uu____2506 =
                     let uu____2508 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2508
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2506)  in
                 FStar_Errors.log_issue uu____2496 uu____2500);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2483
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2531  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___383_2542 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___383_2542.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___383_2542.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___383_2542.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___383_2542.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___383_2542.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___383_2542.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___383_2542.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___383_2542.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___383_2542.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___383_2542.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___383_2542.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___383_2542.FStar_Tactics_Types.local_state)
           }  in
         let uu____2544 = set ps1  in
         bind uu____2544
           (fun uu____2549  ->
              let uu____2550 = FStar_BigInt.of_int_fs n1  in ret uu____2550))
  
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
              let uu____2588 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2588 phi  in
            let uu____2589 = new_uvar reason env typ  in
            bind uu____2589
              (fun uu____2604  ->
                 match uu____2604 with
                 | (uu____2611,ctx_uvar) ->
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
             (fun uu____2658  ->
                let uu____2659 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2659)
             (fun uu____2664  ->
                let e1 =
                  let uu___384_2666 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___384_2666.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___384_2666.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___384_2666.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___384_2666.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___384_2666.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___384_2666.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___384_2666.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___384_2666.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___384_2666.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___384_2666.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___384_2666.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___384_2666.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___384_2666.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___384_2666.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___384_2666.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___384_2666.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___384_2666.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___384_2666.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___384_2666.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___384_2666.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___384_2666.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___384_2666.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___384_2666.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___384_2666.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___384_2666.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___384_2666.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___384_2666.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___384_2666.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___384_2666.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___384_2666.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___384_2666.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___384_2666.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___384_2666.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___384_2666.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___384_2666.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___384_2666.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___384_2666.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___384_2666.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___384_2666.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___384_2666.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___384_2666.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___384_2666.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___386_2678  ->
                     match () with
                     | () ->
                         let uu____2687 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2687) ()
                with
                | FStar_Errors.Err (uu____2714,msg) ->
                    let uu____2718 = tts e1 t  in
                    let uu____2720 =
                      let uu____2722 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2722
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2718 uu____2720 msg
                | FStar_Errors.Error (uu____2732,msg,uu____2734) ->
                    let uu____2737 = tts e1 t  in
                    let uu____2739 =
                      let uu____2741 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2741
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2737 uu____2739 msg))
  
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
             (fun uu____2794  ->
                let uu____2795 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2795)
             (fun uu____2800  ->
                let e1 =
                  let uu___387_2802 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___387_2802.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___387_2802.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___387_2802.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___387_2802.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___387_2802.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___387_2802.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___387_2802.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___387_2802.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___387_2802.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___387_2802.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___387_2802.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___387_2802.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___387_2802.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___387_2802.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___387_2802.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___387_2802.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___387_2802.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___387_2802.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___387_2802.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___387_2802.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___387_2802.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___387_2802.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___387_2802.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___387_2802.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___387_2802.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___387_2802.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___387_2802.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___387_2802.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___387_2802.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___387_2802.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___387_2802.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___387_2802.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___387_2802.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___387_2802.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___387_2802.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___387_2802.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___387_2802.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___387_2802.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___387_2802.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___387_2802.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___387_2802.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___387_2802.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___389_2817  ->
                     match () with
                     | () ->
                         let uu____2826 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2826 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2864,msg) ->
                    let uu____2868 = tts e1 t  in
                    let uu____2870 =
                      let uu____2872 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2872
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2868 uu____2870 msg
                | FStar_Errors.Error (uu____2882,msg,uu____2884) ->
                    let uu____2887 = tts e1 t  in
                    let uu____2889 =
                      let uu____2891 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2891
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2887 uu____2889 msg))
  
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
             (fun uu____2944  ->
                let uu____2945 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2945)
             (fun uu____2951  ->
                let e1 =
                  let uu___390_2953 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___390_2953.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___390_2953.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___390_2953.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___390_2953.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___390_2953.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___390_2953.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___390_2953.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___390_2953.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___390_2953.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___390_2953.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___390_2953.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___390_2953.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___390_2953.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___390_2953.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___390_2953.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___390_2953.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___390_2953.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___390_2953.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___390_2953.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___390_2953.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___390_2953.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___390_2953.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___390_2953.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___390_2953.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___390_2953.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___390_2953.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___390_2953.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___390_2953.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___390_2953.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___390_2953.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___390_2953.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___390_2953.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___390_2953.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___390_2953.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___390_2953.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___390_2953.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___390_2953.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___390_2953.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___390_2953.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___390_2953.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___390_2953.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___390_2953.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___391_2956 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___391_2956.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___391_2956.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___391_2956.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___391_2956.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___391_2956.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___391_2956.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___391_2956.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___391_2956.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___391_2956.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___391_2956.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___391_2956.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___391_2956.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___391_2956.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___391_2956.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___391_2956.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___391_2956.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___391_2956.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___391_2956.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___391_2956.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___391_2956.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___391_2956.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___391_2956.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___391_2956.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___391_2956.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___391_2956.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___391_2956.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___391_2956.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___391_2956.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___391_2956.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___391_2956.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___391_2956.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___391_2956.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___391_2956.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___391_2956.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___391_2956.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___391_2956.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___391_2956.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___391_2956.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___391_2956.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___391_2956.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___391_2956.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___391_2956.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___393_2971  ->
                     match () with
                     | () ->
                         let uu____2980 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2980 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3018,msg) ->
                    let uu____3022 = tts e2 t  in
                    let uu____3024 =
                      let uu____3026 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3026
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3022 uu____3024 msg
                | FStar_Errors.Error (uu____3036,msg,uu____3038) ->
                    let uu____3041 = tts e2 t  in
                    let uu____3043 =
                      let uu____3045 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3045
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3041 uu____3043 msg))
  
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
  fun uu____3079  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___394_3098 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___394_3098.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___394_3098.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___394_3098.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___394_3098.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___394_3098.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___394_3098.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___394_3098.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___394_3098.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___394_3098.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___394_3098.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___394_3098.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___394_3098.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3123 = get_guard_policy ()  in
      bind uu____3123
        (fun old_pol  ->
           let uu____3129 = set_guard_policy pol  in
           bind uu____3129
             (fun uu____3133  ->
                bind t
                  (fun r  ->
                     let uu____3137 = set_guard_policy old_pol  in
                     bind uu____3137 (fun uu____3141  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3145 = let uu____3150 = cur_goal ()  in trytac uu____3150  in
  bind uu____3145
    (fun uu___357_3157  ->
       match uu___357_3157 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3163 = FStar_Options.peek ()  in ret uu____3163)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3188  ->
             let uu____3189 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3189)
          (fun uu____3194  ->
             let uu____3195 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3195
               (fun uu____3199  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3203 =
                         let uu____3204 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3204.FStar_TypeChecker_Env.guard_f  in
                       match uu____3203 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3208 = istrivial e f  in
                           if uu____3208
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3221 =
                                          let uu____3227 =
                                            let uu____3229 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3229
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3227)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3221);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3235  ->
                                           let uu____3236 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3236)
                                        (fun uu____3241  ->
                                           let uu____3242 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3242
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___395_3250 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___395_3250.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___395_3250.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___395_3250.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___395_3250.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3254  ->
                                           let uu____3255 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3255)
                                        (fun uu____3260  ->
                                           let uu____3261 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3261
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___396_3269 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___396_3269.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___396_3269.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___396_3269.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___396_3269.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3273  ->
                                           let uu____3274 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3274)
                                        (fun uu____3278  ->
                                           try
                                             (fun uu___398_3283  ->
                                                match () with
                                                | () ->
                                                    let uu____3286 =
                                                      let uu____3288 =
                                                        let uu____3290 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3290
                                                         in
                                                      Prims.op_Negation
                                                        uu____3288
                                                       in
                                                    if uu____3286
                                                    then
                                                      mlog
                                                        (fun uu____3297  ->
                                                           let uu____3298 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3298)
                                                        (fun uu____3302  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___397_3307 ->
                                               mlog
                                                 (fun uu____3312  ->
                                                    let uu____3313 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3313)
                                                 (fun uu____3317  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3329 =
      let uu____3332 = cur_goal ()  in
      bind uu____3332
        (fun goal  ->
           let uu____3338 =
             let uu____3347 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3347 t  in
           bind uu____3338
             (fun uu____3358  ->
                match uu____3358 with
                | (uu____3367,typ,uu____3369) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____3329
  
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
            let uu____3409 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3409 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3421  ->
    let uu____3424 = cur_goal ()  in
    bind uu____3424
      (fun goal  ->
         let uu____3430 =
           let uu____3432 = FStar_Tactics_Types.goal_env goal  in
           let uu____3433 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3432 uu____3433  in
         if uu____3430
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3439 =
              let uu____3441 = FStar_Tactics_Types.goal_env goal  in
              let uu____3442 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3441 uu____3442  in
            fail1 "Not a trivial goal: %s" uu____3439))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3493 =
               try
                 (fun uu___403_3516  ->
                    match () with
                    | () ->
                        let uu____3527 =
                          let uu____3536 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3536
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3527) ()
               with | uu___402_3547 -> fail "divide: not enough goals"  in
             bind uu____3493
               (fun uu____3584  ->
                  match uu____3584 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___399_3610 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___399_3610.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___399_3610.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___399_3610.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___399_3610.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___399_3610.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___399_3610.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___399_3610.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___399_3610.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___399_3610.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___399_3610.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___399_3610.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3611 = set lp  in
                      bind uu____3611
                        (fun uu____3619  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___400_3635 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___400_3635.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___400_3635.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___400_3635.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___400_3635.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___400_3635.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___400_3635.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___400_3635.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___400_3635.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___400_3635.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___400_3635.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___400_3635.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3636 = set rp  in
                                     bind uu____3636
                                       (fun uu____3644  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___401_3660 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___401_3660.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___401_3660.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3661 = set p'
                                                       in
                                                    bind uu____3661
                                                      (fun uu____3669  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3675 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3697 = divide FStar_BigInt.one f idtac  in
    bind uu____3697
      (fun uu____3710  -> match uu____3710 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3748::uu____3749 ->
             let uu____3752 =
               let uu____3761 = map tau  in
               divide FStar_BigInt.one tau uu____3761  in
             bind uu____3752
               (fun uu____3779  ->
                  match uu____3779 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3821 =
        bind t1
          (fun uu____3826  ->
             let uu____3827 = map t2  in
             bind uu____3827 (fun uu____3835  -> ret ()))
         in
      focus uu____3821
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3845  ->
    let uu____3848 =
      let uu____3851 = cur_goal ()  in
      bind uu____3851
        (fun goal  ->
           let uu____3860 =
             let uu____3867 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3867  in
           match uu____3860 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3876 =
                 let uu____3878 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3878  in
               if uu____3876
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3887 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3887 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3901 = new_uvar "intro" env' typ'  in
                  bind uu____3901
                    (fun uu____3918  ->
                       match uu____3918 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3942 = set_solution goal sol  in
                           bind uu____3942
                             (fun uu____3948  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3950 =
                                  let uu____3953 = bnorm_goal g  in
                                  replace_cur uu____3953  in
                                bind uu____3950 (fun uu____3955  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3960 =
                 let uu____3962 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3963 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3962 uu____3963  in
               fail1 "goal is not an arrow (%s)" uu____3960)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3848
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____3981  ->
    let uu____3988 = cur_goal ()  in
    bind uu____3988
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4007 =
            let uu____4014 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4014  in
          match uu____4007 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4027 =
                let uu____4029 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4029  in
              if uu____4027
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4046 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4046
                    in
                 let bs =
                   let uu____4057 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4057; b]  in
                 let env' =
                   let uu____4083 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4083 bs  in
                 let uu____4084 =
                   let uu____4091 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____4091  in
                 bind uu____4084
                   (fun uu____4111  ->
                      match uu____4111 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4125 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4128 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4125
                              FStar_Parser_Const.effect_Tot_lid uu____4128 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4146 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4146 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4168 =
                                   let uu____4169 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4169.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4168
                                  in
                               let uu____4185 = set_solution goal tm  in
                               bind uu____4185
                                 (fun uu____4194  ->
                                    let uu____4195 =
                                      let uu____4198 =
                                        bnorm_goal
                                          (let uu___404_4201 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___404_4201.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___404_4201.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___404_4201.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___404_4201.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4198  in
                                    bind uu____4195
                                      (fun uu____4208  ->
                                         let uu____4209 =
                                           let uu____4214 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4214, b)  in
                                         ret uu____4209)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4223 =
                let uu____4225 = FStar_Tactics_Types.goal_env goal  in
                let uu____4226 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4225 uu____4226  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4223))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4246 = cur_goal ()  in
    bind uu____4246
      (fun goal  ->
         mlog
           (fun uu____4253  ->
              let uu____4254 =
                let uu____4256 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4256  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4254)
           (fun uu____4262  ->
              let steps =
                let uu____4266 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4266
                 in
              let t =
                let uu____4270 = FStar_Tactics_Types.goal_env goal  in
                let uu____4271 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4270 uu____4271  in
              let uu____4272 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4272))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4297 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4305 -> g.FStar_Tactics_Types.opts
                 | uu____4308 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4313  ->
                    let uu____4314 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4314)
                 (fun uu____4319  ->
                    let uu____4320 = __tc_lax e t  in
                    bind uu____4320
                      (fun uu____4341  ->
                         match uu____4341 with
                         | (t1,uu____4351,uu____4352) ->
                             let steps =
                               let uu____4356 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4356
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4362  ->
                                  let uu____4363 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4363)
                               (fun uu____4367  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4297
  
let (refine_intro : unit -> unit tac) =
  fun uu____4380  ->
    let uu____4383 =
      let uu____4386 = cur_goal ()  in
      bind uu____4386
        (fun g  ->
           let uu____4393 =
             let uu____4404 = FStar_Tactics_Types.goal_env g  in
             let uu____4405 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4404 uu____4405
              in
           match uu____4393 with
           | (uu____4408,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4434 =
                 let uu____4439 =
                   let uu____4444 =
                     let uu____4445 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4445]  in
                   FStar_Syntax_Subst.open_term uu____4444 phi  in
                 match uu____4439 with
                 | (bvs,phi1) ->
                     let uu____4470 =
                       let uu____4471 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4471  in
                     (uu____4470, phi1)
                  in
               (match uu____4434 with
                | (bv1,phi1) ->
                    let uu____4490 =
                      let uu____4493 = FStar_Tactics_Types.goal_env g  in
                      let uu____4494 =
                        let uu____4495 =
                          let uu____4498 =
                            let uu____4499 =
                              let uu____4506 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4506)  in
                            FStar_Syntax_Syntax.NT uu____4499  in
                          [uu____4498]  in
                        FStar_Syntax_Subst.subst uu____4495 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4493
                        uu____4494 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4490
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4515  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4383
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4538 = cur_goal ()  in
      bind uu____4538
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4547 = FStar_Tactics_Types.goal_env goal  in
               let uu____4548 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4547 uu____4548
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4551 = __tc env t  in
           bind uu____4551
             (fun uu____4570  ->
                match uu____4570 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4585  ->
                         let uu____4586 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4588 =
                           let uu____4590 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4590
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4586 uu____4588)
                      (fun uu____4594  ->
                         let uu____4595 =
                           let uu____4598 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4598 guard  in
                         bind uu____4595
                           (fun uu____4601  ->
                              mlog
                                (fun uu____4605  ->
                                   let uu____4606 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4608 =
                                     let uu____4610 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4610
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4606 uu____4608)
                                (fun uu____4614  ->
                                   let uu____4615 =
                                     let uu____4619 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4620 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4619 typ uu____4620  in
                                   bind uu____4615
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4630 =
                                             let uu____4632 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4632 t1  in
                                           let uu____4633 =
                                             let uu____4635 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4635 typ  in
                                           let uu____4636 =
                                             let uu____4638 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4639 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4638 uu____4639  in
                                           let uu____4640 =
                                             let uu____4642 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4643 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4642 uu____4643  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4630 uu____4633 uu____4636
                                             uu____4640)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____4669 =
          mlog
            (fun uu____4674  ->
               let uu____4675 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____4675)
            (fun uu____4680  ->
               let uu____4681 =
                 let uu____4688 = __exact_now set_expected_typ1 tm  in
                 catch uu____4688  in
               bind uu____4681
                 (fun uu___359_4697  ->
                    match uu___359_4697 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4708  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4712  ->
                             let uu____4713 =
                               let uu____4720 =
                                 let uu____4723 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4723
                                   (fun uu____4728  ->
                                      let uu____4729 = refine_intro ()  in
                                      bind uu____4729
                                        (fun uu____4733  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4720  in
                             bind uu____4713
                               (fun uu___358_4740  ->
                                  match uu___358_4740 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4749  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4752  -> ret ())
                                  | FStar_Util.Inl uu____4753 ->
                                      mlog
                                        (fun uu____4755  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4758  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____4669
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4810 = f x  in
          bind uu____4810
            (fun y  ->
               let uu____4818 = mapM f xs  in
               bind uu____4818 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4890 = do_unify e ty1 ty2  in
          bind uu____4890
            (fun uu___360_4904  ->
               if uu___360_4904
               then ret acc
               else
                 (let uu____4924 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4924 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4945 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4947 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4945
                        uu____4947
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4964 =
                        let uu____4966 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4966  in
                      if uu____4964
                      then fail "Codomain is effectful"
                      else
                        (let uu____4990 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4990
                           (fun uu____5017  ->
                              match uu____5017 with
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
      let uu____5107 =
        mlog
          (fun uu____5112  ->
             let uu____5113 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5113)
          (fun uu____5118  ->
             let uu____5119 = cur_goal ()  in
             bind uu____5119
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5127 = __tc e tm  in
                  bind uu____5127
                    (fun uu____5148  ->
                       match uu____5148 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5161 =
                             let uu____5172 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5172  in
                           bind uu____5161
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5215  ->
                                       fun w  ->
                                         match uu____5215 with
                                         | (uvt,q,uu____5233) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5265 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5282  ->
                                       fun s  ->
                                         match uu____5282 with
                                         | (uu____5294,uu____5295,uv) ->
                                             let uu____5297 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5297) uvs uu____5265
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5307 = solve' goal w  in
                                bind uu____5307
                                  (fun uu____5312  ->
                                     let uu____5313 =
                                       mapM
                                         (fun uu____5330  ->
                                            match uu____5330 with
                                            | (uvt,q,uv) ->
                                                let uu____5342 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5342 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5347 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5348 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5348
                                                     then ret ()
                                                     else
                                                       (let uu____5355 =
                                                          let uu____5358 =
                                                            bnorm_goal
                                                              (let uu___405_5361
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___405_5361.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___405_5361.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___405_5361.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5358]  in
                                                        add_goals uu____5355)))
                                         uvs
                                        in
                                     bind uu____5313
                                       (fun uu____5366  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5107
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5394 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5394
    then
      let uu____5403 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5418 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5471 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5403 with
      | (pre,post) ->
          let post1 =
            let uu____5504 =
              let uu____5515 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5515]  in
            FStar_Syntax_Util.mk_app post uu____5504  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5546 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5546
       then
         let uu____5555 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5555
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____5590 =
      let uu____5593 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____5600  ->
                  let uu____5601 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____5601)
               (fun uu____5607  ->
                  let is_unit_t t =
                    let uu____5615 =
                      let uu____5616 = FStar_Syntax_Subst.compress t  in
                      uu____5616.FStar_Syntax_Syntax.n  in
                    match uu____5615 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____5622 -> false  in
                  let uu____5624 = cur_goal ()  in
                  bind uu____5624
                    (fun goal  ->
                       let uu____5630 =
                         let uu____5639 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____5639 tm  in
                       bind uu____5630
                         (fun uu____5654  ->
                            match uu____5654 with
                            | (tm1,t,guard) ->
                                let uu____5666 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____5666 with
                                 | (bs,comp) ->
                                     let uu____5699 = lemma_or_sq comp  in
                                     (match uu____5699 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____5719 =
                                            FStar_List.fold_left
                                              (fun uu____5767  ->
                                                 fun uu____5768  ->
                                                   match (uu____5767,
                                                           uu____5768)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5881 =
                                                         is_unit_t b_t  in
                                                       if uu____5881
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5922 =
                                                            let uu____5935 =
                                                              let uu____5936
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5936.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5939 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5935
                                                              uu____5939 b_t
                                                             in
                                                          match uu____5922
                                                          with
                                                          | (u,uu____5958,g_u)
                                                              ->
                                                              let uu____5972
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5972,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____5719 with
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
                                               let uu____6051 =
                                                 let uu____6055 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____6056 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____6057 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____6055
                                                   uu____6056 uu____6057
                                                  in
                                               bind uu____6051
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____6068 =
                                                        let uu____6070 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____6070 tm1
                                                         in
                                                      let uu____6071 =
                                                        let uu____6073 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____6074 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____6073
                                                          uu____6074
                                                         in
                                                      let uu____6075 =
                                                        let uu____6077 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____6078 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____6077
                                                          uu____6078
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____6068 uu____6071
                                                        uu____6075
                                                    else
                                                      (let uu____6082 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____6082
                                                         (fun uu____6087  ->
                                                            let uu____6088 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____6088
                                                              (fun uu____6096
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____6122
                                                                    =
                                                                    let uu____6125
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6125
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6122
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
                                                                    let uu____6161
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6161)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____6178
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____6178
                                                                   with
                                                                   | 
                                                                   (hd1,uu____6197)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6224)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6241
                                                                    -> false)
                                                                    in
                                                                 let uu____6243
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
                                                                    let uu____6273
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____6273
                                                                    with
                                                                    | 
                                                                    (hd1,uu____6295)
                                                                    ->
                                                                    let uu____6320
                                                                    =
                                                                    let uu____6321
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____6321.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____6320
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____6329)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___406_6349
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___406_6349.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___406_6349.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___406_6349.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___406_6349.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____6352
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____6358
                                                                     ->
                                                                    let uu____6359
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____6361
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____6359
                                                                    uu____6361)
                                                                    (fun
                                                                    uu____6368
                                                                     ->
                                                                    let env =
                                                                    let uu___407_6370
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___407_6370.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____6373
                                                                    =
                                                                    let uu____6376
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____6380
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____6382
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____6380
                                                                    uu____6382
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____6388
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____6376
                                                                    uu____6388
                                                                    g_typ  in
                                                                    bind
                                                                    uu____6373
                                                                    (fun
                                                                    uu____6392
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____6243
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
                                                                    let uu____6456
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____6456
                                                                    then
                                                                    let uu____6461
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____6461
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
                                                                    let uu____6476
                                                                    =
                                                                    let uu____6478
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____6478
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____6476)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____6479
                                                                    =
                                                                    let uu____6482
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____6482
                                                                    guard  in
                                                                    bind
                                                                    uu____6479
                                                                    (fun
                                                                    uu____6486
                                                                     ->
                                                                    let uu____6487
                                                                    =
                                                                    let uu____6490
                                                                    =
                                                                    let uu____6492
                                                                    =
                                                                    let uu____6494
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6495
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____6494
                                                                    uu____6495
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____6492
                                                                     in
                                                                    if
                                                                    uu____6490
                                                                    then
                                                                    let uu____6499
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____6499
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____6487
                                                                    (fun
                                                                    uu____6504
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____5593  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____5590
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____6528 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____6528 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____6538::(e1,uu____6540)::(e2,uu____6542)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____6603 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____6628 = destruct_eq' typ  in
    match uu____6628 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____6658 = FStar_Syntax_Util.un_squash typ  in
        (match uu____6658 with
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
        let uu____6727 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____6727 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____6785 = aux e'  in
               FStar_Util.map_opt uu____6785
                 (fun uu____6816  ->
                    match uu____6816 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____6842 = aux e  in
      FStar_Util.map_opt uu____6842
        (fun uu____6873  ->
           match uu____6873 with
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
          let uu____6947 =
            let uu____6958 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6958  in
          FStar_Util.map_opt uu____6947
            (fun uu____6976  ->
               match uu____6976 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___408_6998 = bv  in
                     let uu____6999 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___408_6998.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___408_6998.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6999
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___409_7007 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7008 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7017 =
                       let uu____7020 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7020  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___409_7007.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7008;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7017;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___409_7007.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___409_7007.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___409_7007.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___409_7007.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___410_7021 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___410_7021.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___410_7021.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___410_7021.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___410_7021.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7032 =
      let uu____7035 = cur_goal ()  in
      bind uu____7035
        (fun goal  ->
           let uu____7043 = h  in
           match uu____7043 with
           | (bv,uu____7047) ->
               mlog
                 (fun uu____7055  ->
                    let uu____7056 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____7058 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____7056
                      uu____7058)
                 (fun uu____7063  ->
                    let uu____7064 =
                      let uu____7075 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____7075  in
                    match uu____7064 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____7102 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____7102 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____7117 =
                               let uu____7118 = FStar_Syntax_Subst.compress x
                                  in
                               uu____7118.FStar_Syntax_Syntax.n  in
                             (match uu____7117 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___411_7135 = bv2  in
                                    let uu____7136 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___411_7135.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___411_7135.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7136
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___412_7144 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____7145 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____7154 =
                                      let uu____7157 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____7157
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___412_7144.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____7145;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____7154;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___412_7144.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___412_7144.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___412_7144.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___412_7144.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___413_7160 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___413_7160.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___413_7160.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___413_7160.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___413_7160.FStar_Tactics_Types.label)
                                     })
                              | uu____7161 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____7163 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7032
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____7193 =
        let uu____7196 = cur_goal ()  in
        bind uu____7196
          (fun goal  ->
             let uu____7207 = b  in
             match uu____7207 with
             | (bv,uu____7211) ->
                 let bv' =
                   let uu____7217 =
                     let uu___414_7218 = bv  in
                     let uu____7219 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____7219;
                       FStar_Syntax_Syntax.index =
                         (uu___414_7218.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___414_7218.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____7217  in
                 let s1 =
                   let uu____7224 =
                     let uu____7225 =
                       let uu____7232 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____7232)  in
                     FStar_Syntax_Syntax.NT uu____7225  in
                   [uu____7224]  in
                 let uu____7237 = subst_goal bv bv' s1 goal  in
                 (match uu____7237 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____7193
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____7259 =
      let uu____7262 = cur_goal ()  in
      bind uu____7262
        (fun goal  ->
           let uu____7271 = b  in
           match uu____7271 with
           | (bv,uu____7275) ->
               let uu____7280 =
                 let uu____7291 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____7291  in
               (match uu____7280 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____7318 = FStar_Syntax_Util.type_u ()  in
                    (match uu____7318 with
                     | (ty,u) ->
                         let uu____7327 = new_uvar "binder_retype" e0 ty  in
                         bind uu____7327
                           (fun uu____7346  ->
                              match uu____7346 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___415_7356 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___415_7356.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___415_7356.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____7360 =
                                      let uu____7361 =
                                        let uu____7368 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____7368)  in
                                      FStar_Syntax_Syntax.NT uu____7361  in
                                    [uu____7360]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___416_7380 = b1  in
                                         let uu____7381 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___416_7380.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___416_7380.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____7381
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____7388  ->
                                       let new_goal =
                                         let uu____7390 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____7391 =
                                           let uu____7392 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____7392
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7390 uu____7391
                                          in
                                       let uu____7393 = add_goals [new_goal]
                                          in
                                       bind uu____7393
                                         (fun uu____7398  ->
                                            let uu____7399 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____7399
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____7259
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____7425 =
        let uu____7428 = cur_goal ()  in
        bind uu____7428
          (fun goal  ->
             let uu____7437 = b  in
             match uu____7437 with
             | (bv,uu____7441) ->
                 let uu____7446 =
                   let uu____7457 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____7457  in
                 (match uu____7446 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____7487 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____7487
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___417_7492 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___417_7492.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___417_7492.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____7494 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____7494))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____7425
  
let (revert : unit -> unit tac) =
  fun uu____7507  ->
    let uu____7510 = cur_goal ()  in
    bind uu____7510
      (fun goal  ->
         let uu____7516 =
           let uu____7523 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7523  in
         match uu____7516 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____7540 =
                 let uu____7543 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____7543  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____7540
                in
             let uu____7558 = new_uvar "revert" env' typ'  in
             bind uu____7558
               (fun uu____7574  ->
                  match uu____7574 with
                  | (r,u_r) ->
                      let uu____7583 =
                        let uu____7586 =
                          let uu____7587 =
                            let uu____7588 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____7588.FStar_Syntax_Syntax.pos  in
                          let uu____7591 =
                            let uu____7596 =
                              let uu____7597 =
                                let uu____7606 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____7606  in
                              [uu____7597]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____7596  in
                          uu____7591 FStar_Pervasives_Native.None uu____7587
                           in
                        set_solution goal uu____7586  in
                      bind uu____7583
                        (fun uu____7627  ->
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
      let uu____7641 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7641
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____7657 = cur_goal ()  in
    bind uu____7657
      (fun goal  ->
         mlog
           (fun uu____7665  ->
              let uu____7666 = FStar_Syntax_Print.binder_to_string b  in
              let uu____7668 =
                let uu____7670 =
                  let uu____7672 =
                    let uu____7681 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____7681  in
                  FStar_All.pipe_right uu____7672 FStar_List.length  in
                FStar_All.pipe_right uu____7670 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____7666 uu____7668)
           (fun uu____7702  ->
              let uu____7703 =
                let uu____7714 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____7714  in
              match uu____7703 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____7759 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____7759
                        then
                          let uu____7764 =
                            let uu____7766 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____7766
                             in
                          fail uu____7764
                        else check1 bvs2
                     in
                  let uu____7771 =
                    let uu____7773 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____7773  in
                  if uu____7771
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____7780 = check1 bvs  in
                     bind uu____7780
                       (fun uu____7786  ->
                          let env' = push_bvs e' bvs  in
                          let uu____7788 =
                            let uu____7795 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____7795  in
                          bind uu____7788
                            (fun uu____7805  ->
                               match uu____7805 with
                               | (ut,uvar_ut) ->
                                   let uu____7814 = set_solution goal ut  in
                                   bind uu____7814
                                     (fun uu____7819  ->
                                        let uu____7820 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____7820))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____7828  ->
    let uu____7831 = cur_goal ()  in
    bind uu____7831
      (fun goal  ->
         let uu____7837 =
           let uu____7844 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7844  in
         match uu____7837 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____7853) ->
             let uu____7858 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____7858)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____7871 = cur_goal ()  in
    bind uu____7871
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7881 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7881  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7884  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____7897 = cur_goal ()  in
    bind uu____7897
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7907 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7907  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7910  -> add_goals [g']))
  
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
            let uu____7951 = FStar_Syntax_Subst.compress t  in
            uu____7951.FStar_Syntax_Syntax.n  in
          let uu____7954 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___421_7961 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___421_7961.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___421_7961.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____7954
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7978 =
                   let uu____7979 = FStar_Syntax_Subst.compress t1  in
                   uu____7979.FStar_Syntax_Syntax.n  in
                 match uu____7978 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8010 = ff hd1  in
                     bind uu____8010
                       (fun hd2  ->
                          let fa uu____8036 =
                            match uu____8036 with
                            | (a,q) ->
                                let uu____8057 = ff a  in
                                bind uu____8057 (fun a1  -> ret (a1, q))
                             in
                          let uu____8076 = mapM fa args  in
                          bind uu____8076
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____8158 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____8158 with
                      | (bs1,t') ->
                          let uu____8167 =
                            let uu____8170 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____8170 t'  in
                          bind uu____8167
                            (fun t''  ->
                               let uu____8174 =
                                 let uu____8175 =
                                   let uu____8194 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____8203 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____8194, uu____8203, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____8175  in
                               ret uu____8174))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____8278 = ff hd1  in
                     bind uu____8278
                       (fun hd2  ->
                          let ffb br =
                            let uu____8293 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____8293 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____8325 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____8325  in
                                let uu____8326 = ff1 e  in
                                bind uu____8326
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____8341 = mapM ffb brs  in
                          bind uu____8341
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____8385;
                          FStar_Syntax_Syntax.lbtyp = uu____8386;
                          FStar_Syntax_Syntax.lbeff = uu____8387;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____8389;
                          FStar_Syntax_Syntax.lbpos = uu____8390;_}::[]),e)
                     ->
                     let lb =
                       let uu____8418 =
                         let uu____8419 = FStar_Syntax_Subst.compress t1  in
                         uu____8419.FStar_Syntax_Syntax.n  in
                       match uu____8418 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____8423) -> lb
                       | uu____8439 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____8449 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8449
                         (fun def1  ->
                            ret
                              (let uu___418_8455 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___418_8455.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___418_8455.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___418_8455.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___418_8455.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___418_8455.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___418_8455.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8456 = fflb lb  in
                     bind uu____8456
                       (fun lb1  ->
                          let uu____8466 =
                            let uu____8471 =
                              let uu____8472 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____8472]  in
                            FStar_Syntax_Subst.open_term uu____8471 e  in
                          match uu____8466 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____8502 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____8502  in
                              let uu____8503 = ff1 e1  in
                              bind uu____8503
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____8550 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8550
                         (fun def  ->
                            ret
                              (let uu___419_8556 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___419_8556.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___419_8556.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___419_8556.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___419_8556.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___419_8556.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___419_8556.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8557 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____8557 with
                      | (lbs1,e1) ->
                          let uu____8572 = mapM fflb lbs1  in
                          bind uu____8572
                            (fun lbs2  ->
                               let uu____8584 = ff e1  in
                               bind uu____8584
                                 (fun e2  ->
                                    let uu____8592 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____8592 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____8663 = ff t2  in
                     bind uu____8663
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____8694 = ff t2  in
                     bind uu____8694
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____8701 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___420_8708 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___420_8708.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___420_8708.FStar_Syntax_Syntax.vars)
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
              let uu____8755 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___422_8764 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___422_8764.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___422_8764.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___422_8764.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___422_8764.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___422_8764.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___422_8764.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___422_8764.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___422_8764.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___422_8764.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___422_8764.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___422_8764.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___422_8764.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___422_8764.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___422_8764.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___422_8764.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___422_8764.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___422_8764.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___422_8764.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___422_8764.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___422_8764.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___422_8764.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___422_8764.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___422_8764.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___422_8764.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___422_8764.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___422_8764.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___422_8764.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___422_8764.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___422_8764.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___422_8764.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___422_8764.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___422_8764.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___422_8764.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___422_8764.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___422_8764.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___422_8764.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___422_8764.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___422_8764.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___422_8764.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___422_8764.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___422_8764.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___422_8764.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____8755 with
              | (t1,lcomp,g) ->
                  let uu____8771 =
                    (let uu____8775 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____8775) ||
                      (let uu____8778 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____8778)
                     in
                  if uu____8771
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____8789 = new_uvar "pointwise_rec" env typ  in
                       bind uu____8789
                         (fun uu____8806  ->
                            match uu____8806 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____8819  ->
                                      let uu____8820 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____8822 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____8820 uu____8822);
                                 (let uu____8825 =
                                    let uu____8828 =
                                      let uu____8829 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____8829 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____8828
                                      opts label1
                                     in
                                  bind uu____8825
                                    (fun uu____8833  ->
                                       let uu____8834 =
                                         bind tau
                                           (fun uu____8840  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____8846  ->
                                                   let uu____8847 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____8849 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____8847 uu____8849);
                                              ret ut1)
                                          in
                                       focus uu____8834))))
                        in
                     let uu____8852 = catch rewrite_eq  in
                     bind uu____8852
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
          let uu____9070 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____9070
            (fun t1  ->
               let uu____9078 =
                 f env
                   (let uu___425_9087 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___425_9087.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___425_9087.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____9078
                 (fun uu____9103  ->
                    match uu____9103 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____9126 =
                               let uu____9127 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____9127.FStar_Syntax_Syntax.n  in
                             match uu____9126 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____9164 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____9164
                                   (fun uu____9189  ->
                                      match uu____9189 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____9205 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____9205
                                            (fun uu____9232  ->
                                               match uu____9232 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___423_9262 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___423_9262.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___423_9262.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____9304 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____9304 with
                                  | (bs1,t') ->
                                      let uu____9319 =
                                        let uu____9326 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____9326 ctrl1 t'
                                         in
                                      bind uu____9319
                                        (fun uu____9344  ->
                                           match uu____9344 with
                                           | (t'',ctrl2) ->
                                               let uu____9359 =
                                                 let uu____9366 =
                                                   let uu___424_9369 = t4  in
                                                   let uu____9372 =
                                                     let uu____9373 =
                                                       let uu____9392 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____9401 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____9392,
                                                         uu____9401, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____9373
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____9372;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___424_9369.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___424_9369.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____9366, ctrl2)  in
                                               ret uu____9359))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____9454 -> ret (t3, ctrl1))))

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
              let uu____9501 = ctrl_tac_fold f env ctrl t  in
              bind uu____9501
                (fun uu____9525  ->
                   match uu____9525 with
                   | (t1,ctrl1) ->
                       let uu____9540 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____9540
                         (fun uu____9567  ->
                            match uu____9567 with
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
                let uu____9661 =
                  let uu____9669 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____9669
                    (fun uu____9680  ->
                       let uu____9681 = ctrl t1  in
                       bind uu____9681
                         (fun res  ->
                            let uu____9708 = trivial ()  in
                            bind uu____9708 (fun uu____9717  -> ret res)))
                   in
                bind uu____9661
                  (fun uu____9735  ->
                     match uu____9735 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____9764 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___426_9773 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___426_9773.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___426_9773.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___426_9773.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___426_9773.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___426_9773.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___426_9773.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___426_9773.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___426_9773.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___426_9773.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___426_9773.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___426_9773.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___426_9773.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___426_9773.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___426_9773.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___426_9773.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___426_9773.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___426_9773.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___426_9773.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___426_9773.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___426_9773.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___426_9773.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___426_9773.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___426_9773.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___426_9773.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___426_9773.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___426_9773.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___426_9773.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___426_9773.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___426_9773.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___426_9773.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___426_9773.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___426_9773.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___426_9773.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___426_9773.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___426_9773.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___426_9773.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___426_9773.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___426_9773.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___426_9773.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___426_9773.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___426_9773.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___426_9773.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____9764 with
                            | (t2,lcomp,g) ->
                                let uu____9784 =
                                  (let uu____9788 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____9788) ||
                                    (let uu____9791 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____9791)
                                   in
                                if uu____9784
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____9807 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____9807
                                     (fun uu____9828  ->
                                        match uu____9828 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____9845  ->
                                                  let uu____9846 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____9848 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____9846 uu____9848);
                                             (let uu____9851 =
                                                let uu____9854 =
                                                  let uu____9855 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____9855 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____9854 opts label1
                                                 in
                                              bind uu____9851
                                                (fun uu____9863  ->
                                                   let uu____9864 =
                                                     bind rewriter
                                                       (fun uu____9878  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____9884 
                                                               ->
                                                               let uu____9885
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____9887
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____9885
                                                                 uu____9887);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____9864)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____9933 =
        bind get
          (fun ps  ->
             let uu____9943 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9943 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9981  ->
                       let uu____9982 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____9982);
                  bind dismiss_all
                    (fun uu____9987  ->
                       let uu____9988 =
                         let uu____9995 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9995
                           keepGoing gt1
                          in
                       bind uu____9988
                         (fun uu____10007  ->
                            match uu____10007 with
                            | (gt',uu____10015) ->
                                (log ps
                                   (fun uu____10019  ->
                                      let uu____10020 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10020);
                                 (let uu____10023 = push_goals gs  in
                                  bind uu____10023
                                    (fun uu____10028  ->
                                       let uu____10029 =
                                         let uu____10032 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10032]  in
                                       add_goals uu____10029)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____9933
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10057 =
        bind get
          (fun ps  ->
             let uu____10067 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10067 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10105  ->
                       let uu____10106 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____10106);
                  bind dismiss_all
                    (fun uu____10111  ->
                       let uu____10112 =
                         let uu____10115 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10115 gt1
                          in
                       bind uu____10112
                         (fun gt'  ->
                            log ps
                              (fun uu____10123  ->
                                 let uu____10124 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____10124);
                            (let uu____10127 = push_goals gs  in
                             bind uu____10127
                               (fun uu____10132  ->
                                  let uu____10133 =
                                    let uu____10136 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____10136]  in
                                  add_goals uu____10133))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10057
  
let (trefl : unit -> unit tac) =
  fun uu____10149  ->
    let uu____10152 =
      let uu____10155 = cur_goal ()  in
      bind uu____10155
        (fun g  ->
           let uu____10173 =
             let uu____10178 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____10178  in
           match uu____10173 with
           | FStar_Pervasives_Native.Some t ->
               let uu____10186 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____10186 with
                | (hd1,args) ->
                    let uu____10225 =
                      let uu____10238 =
                        let uu____10239 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____10239.FStar_Syntax_Syntax.n  in
                      (uu____10238, args)  in
                    (match uu____10225 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____10253::(l,uu____10255)::(r,uu____10257)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____10304 =
                           let uu____10308 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____10308 l r  in
                         bind uu____10304
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____10319 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10319 l
                                    in
                                 let r1 =
                                   let uu____10321 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10321 r
                                    in
                                 let uu____10322 =
                                   let uu____10326 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____10326 l1 r1  in
                                 bind uu____10322
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____10336 =
                                           let uu____10338 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10338 l1  in
                                         let uu____10339 =
                                           let uu____10341 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10341 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____10336 uu____10339))))
                     | (hd2,uu____10344) ->
                         let uu____10361 =
                           let uu____10363 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____10363 t  in
                         fail1 "trefl: not an equality (%s)" uu____10361))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____10152
  
let (dup : unit -> unit tac) =
  fun uu____10380  ->
    let uu____10383 = cur_goal ()  in
    bind uu____10383
      (fun g  ->
         let uu____10389 =
           let uu____10396 = FStar_Tactics_Types.goal_env g  in
           let uu____10397 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____10396 uu____10397  in
         bind uu____10389
           (fun uu____10407  ->
              match uu____10407 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___427_10417 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___427_10417.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___427_10417.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___427_10417.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___427_10417.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____10420  ->
                       let uu____10421 =
                         let uu____10424 = FStar_Tactics_Types.goal_env g  in
                         let uu____10425 =
                           let uu____10426 =
                             let uu____10427 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____10428 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____10427
                               uu____10428
                              in
                           let uu____10429 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____10430 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____10426 uu____10429 u
                             uu____10430
                            in
                         add_irrelevant_goal "dup equation" uu____10424
                           uu____10425 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____10421
                         (fun uu____10434  ->
                            let uu____10435 = add_goals [g']  in
                            bind uu____10435 (fun uu____10439  -> ret ())))))
  
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
              let uu____10565 = f x y  in
              if uu____10565 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____10588 -> (acc, l11, l21)  in
        let uu____10603 = aux [] l1 l2  in
        match uu____10603 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____10709 = get_phi g1  in
      match uu____10709 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____10716 = get_phi g2  in
          (match uu____10716 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____10729 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____10729 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____10760 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____10760 phi1  in
                    let t2 =
                      let uu____10770 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____10770 phi2  in
                    let uu____10779 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____10779
                      (fun uu____10784  ->
                         let uu____10785 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____10785
                           (fun uu____10792  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___428_10797 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____10798 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___428_10797.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___428_10797.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___428_10797.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___428_10797.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____10798;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___428_10797.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___428_10797.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___428_10797.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___428_10797.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___428_10797.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___428_10797.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___428_10797.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___428_10797.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___428_10797.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___428_10797.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___428_10797.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___428_10797.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___428_10797.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___428_10797.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___428_10797.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___428_10797.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___428_10797.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___428_10797.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___428_10797.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___428_10797.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___428_10797.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___428_10797.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___428_10797.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___428_10797.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___428_10797.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___428_10797.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___428_10797.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___428_10797.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___428_10797.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___428_10797.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___428_10797.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___428_10797.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___428_10797.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___428_10797.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___428_10797.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___428_10797.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___428_10797.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____10802 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____10802
                                (fun goal  ->
                                   mlog
                                     (fun uu____10812  ->
                                        let uu____10813 =
                                          goal_to_string_verbose g1  in
                                        let uu____10815 =
                                          goal_to_string_verbose g2  in
                                        let uu____10817 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____10813 uu____10815 uu____10817)
                                     (fun uu____10821  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____10829  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____10845 =
               set
                 (let uu___429_10850 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___429_10850.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___429_10850.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___429_10850.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___429_10850.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___429_10850.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___429_10850.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___429_10850.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___429_10850.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___429_10850.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___429_10850.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___429_10850.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___429_10850.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____10845
               (fun uu____10853  ->
                  let uu____10854 = join_goals g1 g2  in
                  bind uu____10854 (fun g12  -> add_goals [g12]))
         | uu____10859 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____10881 =
      let uu____10888 = cur_goal ()  in
      bind uu____10888
        (fun g  ->
           let uu____10898 =
             let uu____10907 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10907 t  in
           bind uu____10898
             (fun uu____10935  ->
                match uu____10935 with
                | (t1,typ,guard) ->
                    let uu____10951 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____10951 with
                     | (hd1,args) ->
                         let uu____11000 =
                           let uu____11015 =
                             let uu____11016 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____11016.FStar_Syntax_Syntax.n  in
                           (uu____11015, args)  in
                         (match uu____11000 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____11037)::(q,uu____11039)::[]) when
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
                                let uu____11093 =
                                  let uu____11094 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11094
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11093
                                 in
                              let g2 =
                                let uu____11096 =
                                  let uu____11097 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11097
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11096
                                 in
                              bind __dismiss
                                (fun uu____11104  ->
                                   let uu____11105 = add_goals [g1; g2]  in
                                   bind uu____11105
                                     (fun uu____11114  ->
                                        let uu____11115 =
                                          let uu____11120 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____11121 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____11120, uu____11121)  in
                                        ret uu____11115))
                          | uu____11126 ->
                              let uu____11141 =
                                let uu____11143 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____11143 typ  in
                              fail1 "Not a disjunction: %s" uu____11141))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____10881
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11178 =
      let uu____11181 = cur_goal ()  in
      bind uu____11181
        (fun g  ->
           FStar_Options.push ();
           (let uu____11194 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11194);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___430_11201 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___430_11201.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___430_11201.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___430_11201.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___430_11201.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11178
  
let (top_env : unit -> env tac) =
  fun uu____11218  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11233  ->
    let uu____11237 = cur_goal ()  in
    bind uu____11237
      (fun g  ->
         let uu____11244 =
           (FStar_Options.lax ()) ||
             (let uu____11247 = FStar_Tactics_Types.goal_env g  in
              uu____11247.FStar_TypeChecker_Env.lax)
            in
         ret uu____11244)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11264 =
        mlog
          (fun uu____11269  ->
             let uu____11270 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11270)
          (fun uu____11275  ->
             let uu____11276 = cur_goal ()  in
             bind uu____11276
               (fun goal  ->
                  let env =
                    let uu____11284 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11284 ty  in
                  let uu____11285 = __tc_ghost env tm  in
                  bind uu____11285
                    (fun uu____11304  ->
                       match uu____11304 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11318  ->
                                let uu____11319 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11319)
                             (fun uu____11323  ->
                                mlog
                                  (fun uu____11326  ->
                                     let uu____11327 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11327)
                                  (fun uu____11332  ->
                                     let uu____11333 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11333
                                       (fun uu____11338  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11264
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11363 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11369 =
              let uu____11376 =
                let uu____11377 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11377
                 in
              new_uvar "uvar_env.2" env uu____11376  in
            bind uu____11369
              (fun uu____11394  ->
                 match uu____11394 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11363
        (fun typ  ->
           let uu____11406 = new_uvar "uvar_env" env typ  in
           bind uu____11406
             (fun uu____11421  ->
                match uu____11421 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____11440 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____11459 -> g.FStar_Tactics_Types.opts
             | uu____11462 -> FStar_Options.peek ()  in
           let uu____11465 = FStar_Syntax_Util.head_and_args t  in
           match uu____11465 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____11485);
                FStar_Syntax_Syntax.pos = uu____11486;
                FStar_Syntax_Syntax.vars = uu____11487;_},uu____11488)
               ->
               let env1 =
                 let uu___431_11530 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___431_11530.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___431_11530.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___431_11530.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___431_11530.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___431_11530.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___431_11530.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___431_11530.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___431_11530.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___431_11530.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___431_11530.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___431_11530.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___431_11530.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___431_11530.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___431_11530.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___431_11530.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___431_11530.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___431_11530.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___431_11530.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___431_11530.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___431_11530.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___431_11530.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___431_11530.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___431_11530.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___431_11530.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___431_11530.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___431_11530.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___431_11530.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___431_11530.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___431_11530.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___431_11530.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___431_11530.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___431_11530.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___431_11530.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___431_11530.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___431_11530.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___431_11530.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___431_11530.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___431_11530.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___431_11530.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___431_11530.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___431_11530.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___431_11530.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____11534 =
                 let uu____11537 = bnorm_goal g  in [uu____11537]  in
               add_goals uu____11534
           | uu____11538 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____11440
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____11600 = if b then t2 else ret false  in
             bind uu____11600 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____11626 = trytac comp  in
      bind uu____11626
        (fun uu___361_11638  ->
           match uu___361_11638 with
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
        let uu____11680 =
          bind get
            (fun ps  ->
               let uu____11688 = __tc e t1  in
               bind uu____11688
                 (fun uu____11709  ->
                    match uu____11709 with
                    | (t11,ty1,g1) ->
                        let uu____11722 = __tc e t2  in
                        bind uu____11722
                          (fun uu____11743  ->
                             match uu____11743 with
                             | (t21,ty2,g2) ->
                                 let uu____11756 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____11756
                                   (fun uu____11763  ->
                                      let uu____11764 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____11764
                                        (fun uu____11772  ->
                                           let uu____11773 =
                                             do_unify e ty1 ty2  in
                                           let uu____11777 =
                                             do_unify e t11 t21  in
                                           tac_and uu____11773 uu____11777)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____11680
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____11825  ->
             let uu____11826 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____11826
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
        (fun uu____11860  ->
           let uu____11861 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____11861)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____11872 =
      mlog
        (fun uu____11877  ->
           let uu____11878 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____11878)
        (fun uu____11883  ->
           let uu____11884 = cur_goal ()  in
           bind uu____11884
             (fun g  ->
                let uu____11890 =
                  let uu____11899 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____11899 ty  in
                bind uu____11890
                  (fun uu____11911  ->
                     match uu____11911 with
                     | (ty1,uu____11921,guard) ->
                         let uu____11923 =
                           let uu____11926 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____11926 guard  in
                         bind uu____11923
                           (fun uu____11930  ->
                              let uu____11931 =
                                let uu____11935 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____11936 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____11935 uu____11936 ty1  in
                              bind uu____11931
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____11945 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____11945
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____11952 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____11953 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____11952
                                          uu____11953
                                         in
                                      let nty =
                                        let uu____11955 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____11955 ty1  in
                                      let uu____11956 =
                                        let uu____11960 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____11960 ng nty  in
                                      bind uu____11956
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____11969 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____11969
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____11872
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12043 =
      let uu____12052 = cur_goal ()  in
      bind uu____12052
        (fun g  ->
           let uu____12064 =
             let uu____12073 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12073 s_tm  in
           bind uu____12064
             (fun uu____12091  ->
                match uu____12091 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12109 =
                      let uu____12112 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12112 guard  in
                    bind uu____12109
                      (fun uu____12125  ->
                         let uu____12126 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12126 with
                         | (h,args) ->
                             let uu____12171 =
                               let uu____12178 =
                                 let uu____12179 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12179.FStar_Syntax_Syntax.n  in
                               match uu____12178 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12194;
                                      FStar_Syntax_Syntax.vars = uu____12195;_},us)
                                   -> ret (fv, us)
                               | uu____12205 -> fail "type is not an fv"  in
                             bind uu____12171
                               (fun uu____12226  ->
                                  match uu____12226 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12242 =
                                        let uu____12245 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12245 t_lid
                                         in
                                      (match uu____12242 with
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
                                                  (fun uu____12296  ->
                                                     let uu____12297 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12297 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12312 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12340
                                                                  =
                                                                  let uu____12343
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12343
                                                                    c_lid
                                                                   in
                                                                match uu____12340
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
                                                                    uu____12417
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
                                                                    let uu____12422
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____12422
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____12445
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____12445
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____12488
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____12488
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____12561
                                                                    =
                                                                    let uu____12563
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____12563
                                                                     in
                                                                    failwhen
                                                                    uu____12561
                                                                    "not total?"
                                                                    (fun
                                                                    uu____12582
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
                                                                    uu___362_12599
                                                                    =
                                                                    match uu___362_12599
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____12603)
                                                                    -> true
                                                                    | 
                                                                    uu____12606
                                                                    -> false
                                                                     in
                                                                    let uu____12610
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____12610
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
                                                                    uu____12744
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
                                                                    uu____12806
                                                                     ->
                                                                    match uu____12806
                                                                    with
                                                                    | 
                                                                    ((bv,uu____12826),
                                                                    (t,uu____12828))
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
                                                                    uu____12898
                                                                     ->
                                                                    match uu____12898
                                                                    with
                                                                    | 
                                                                    ((bv,uu____12925),
                                                                    (t,uu____12927))
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
                                                                    uu____12986
                                                                     ->
                                                                    match uu____12986
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
                                                                    let uu____13041
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___432_13058
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___432_13058.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13041
                                                                    with
                                                                    | 
                                                                    (uu____13072,uu____13073,uu____13074,pat_t,uu____13076,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13083
                                                                    =
                                                                    let uu____13084
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13084
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13083
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13089
                                                                    =
                                                                    let uu____13098
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13098]
                                                                     in
                                                                    let uu____13117
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13089
                                                                    uu____13117
                                                                     in
                                                                    let nty =
                                                                    let uu____13123
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13123
                                                                     in
                                                                    let uu____13126
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13126
                                                                    (fun
                                                                    uu____13156
                                                                     ->
                                                                    match uu____13156
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
                                                                    let uu____13183
                                                                    =
                                                                    let uu____13194
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13194]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13183
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13230
                                                                    =
                                                                    let uu____13241
                                                                    =
                                                                    let uu____13246
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13246)
                                                                     in
                                                                    (g', br,
                                                                    uu____13241)
                                                                     in
                                                                    ret
                                                                    uu____13230))))))
                                                                    | 
                                                                    uu____13267
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12312
                                                           (fun goal_brs  ->
                                                              let uu____13317
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13317
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
                                                                  let uu____13390
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____13390
                                                                    (
                                                                    fun
                                                                    uu____13401
                                                                     ->
                                                                    let uu____13402
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____13402
                                                                    (fun
                                                                    uu____13412
                                                                     ->
                                                                    ret infos))))
                                            | uu____13419 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12043
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____13468::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____13498 = init xs  in x :: uu____13498
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____13511 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____13520) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____13586 = last args  in
          (match uu____13586 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____13616 =
                 let uu____13617 =
                   let uu____13622 =
                     let uu____13623 =
                       let uu____13628 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____13628  in
                     uu____13623 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____13622, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____13617  in
               FStar_All.pipe_left ret uu____13616)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____13641,uu____13642) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____13695 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____13695 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____13737 =
                      let uu____13738 =
                        let uu____13743 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____13743)  in
                      FStar_Reflection_Data.Tv_Abs uu____13738  in
                    FStar_All.pipe_left ret uu____13737))
      | FStar_Syntax_Syntax.Tm_type uu____13746 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____13771 ->
          let uu____13786 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____13786 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____13817 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____13817 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____13870 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____13883 =
            let uu____13884 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____13884  in
          FStar_All.pipe_left ret uu____13883
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____13905 =
            let uu____13906 =
              let uu____13911 =
                let uu____13912 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____13912  in
              (uu____13911, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____13906  in
          FStar_All.pipe_left ret uu____13905
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____13952 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____13957 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____13957 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14010 ->
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
             | FStar_Util.Inr uu____14052 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14056 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14056 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14076 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14082 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14137 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14137
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14158 =
                  let uu____14165 =
                    FStar_List.map
                      (fun uu____14178  ->
                         match uu____14178 with
                         | (p1,uu____14187) -> inspect_pat p1) ps
                     in
                  (fv, uu____14165)  in
                FStar_Reflection_Data.Pat_Cons uu____14158
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
              (fun uu___363_14283  ->
                 match uu___363_14283 with
                 | (pat,uu____14305,t5) ->
                     let uu____14323 = inspect_pat pat  in (uu____14323, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14332 ->
          ((let uu____14334 =
              let uu____14340 =
                let uu____14342 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14344 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14342 uu____14344
                 in
              (FStar_Errors.Warning_CantInspect, uu____14340)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14334);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____13511
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14362 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14362
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14366 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14366
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14370 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14370
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____14377 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____14377
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____14402 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____14402
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____14419 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____14419
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____14438 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____14438
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____14442 =
          let uu____14443 =
            let uu____14450 =
              let uu____14451 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____14451  in
            FStar_Syntax_Syntax.mk uu____14450  in
          uu____14443 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14442
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____14459 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14459
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14470 =
          let uu____14471 =
            let uu____14478 =
              let uu____14479 =
                let uu____14493 =
                  let uu____14496 =
                    let uu____14497 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____14497]  in
                  FStar_Syntax_Subst.close uu____14496 t2  in
                ((false, [lb]), uu____14493)  in
              FStar_Syntax_Syntax.Tm_let uu____14479  in
            FStar_Syntax_Syntax.mk uu____14478  in
          uu____14471 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14470
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14542 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____14542 with
         | (lbs,body) ->
             let uu____14557 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____14557)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____14594 =
                let uu____14595 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____14595  in
              FStar_All.pipe_left wrap uu____14594
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____14602 =
                let uu____14603 =
                  let uu____14617 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____14635 = pack_pat p1  in
                         (uu____14635, false)) ps
                     in
                  (fv, uu____14617)  in
                FStar_Syntax_Syntax.Pat_cons uu____14603  in
              FStar_All.pipe_left wrap uu____14602
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
            (fun uu___364_14684  ->
               match uu___364_14684 with
               | (pat,t1) ->
                   let uu____14701 = pack_pat pat  in
                   (uu____14701, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____14749 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14749
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____14777 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14777
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____14823 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14823
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____14862 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14862
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____14882 =
        bind get
          (fun ps  ->
             let uu____14888 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____14888 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____14882
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____14922 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___433_14929 = ps  in
                 let uu____14930 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___433_14929.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___433_14929.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___433_14929.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___433_14929.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___433_14929.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___433_14929.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___433_14929.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___433_14929.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___433_14929.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___433_14929.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___433_14929.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___433_14929.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____14930
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____14922
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____14957 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____14957 with
      | (u,ctx_uvars,g_u) ->
          let uu____14990 = FStar_List.hd ctx_uvars  in
          (match uu____14990 with
           | (ctx_uvar,uu____15004) ->
               let g =
                 let uu____15006 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15006 false
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
        let uu____15029 = goal_of_goal_ty env typ  in
        match uu____15029 with
        | (g,g_u) ->
            let ps =
              let uu____15041 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15044 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15041;
                FStar_Tactics_Types.local_state = uu____15044
              }  in
            let uu____15054 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15054)
  