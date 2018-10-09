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
        (try (fun uu___368_169  -> match () with | () -> run t p) ()
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
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
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
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
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
                 let uu___369_1372 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___369_1372.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___369_1372.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___369_1372.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___369_1372.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___369_1372.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___369_1372.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___369_1372.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___369_1372.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___369_1372.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___369_1372.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___369_1372.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___369_1372.FStar_Tactics_Types.local_state)
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
           (fun uu___371_1518  ->
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
           (let uu___372_1634 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_1634.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_1634.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___372_1634.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___372_1634.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_1634.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_1634.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_1634.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_1634.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_1634.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_1634.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_1634.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_1634.FStar_Tactics_Types.local_state)
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
           (fun uu___374_1675  ->
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
         let uu___375_1756 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___375_1756.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___375_1756.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___375_1756.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___376_1759 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___376_1759.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___376_1759.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___376_1759.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___376_1759.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___376_1759.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___376_1759.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___376_1759.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___376_1759.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___376_1759.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___376_1759.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___376_1759.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___376_1759.FStar_Tactics_Types.local_state)
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
         let uu___377_1825 = ps  in
         let uu____1826 =
           FStar_List.filter
             (fun g  ->
                let uu____1832 = check_goal_solved g  in
                FStar_Option.isNone uu____1832) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___377_1825.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___377_1825.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___377_1825.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1826;
           FStar_Tactics_Types.smt_goals =
             (uu___377_1825.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___377_1825.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___377_1825.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___377_1825.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___377_1825.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___377_1825.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___377_1825.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___377_1825.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___377_1825.FStar_Tactics_Types.local_state)
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
         let uu___378_1888 = p  in
         let uu____1889 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___378_1888.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___378_1888.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___378_1888.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1889;
           FStar_Tactics_Types.smt_goals =
             (uu___378_1888.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___378_1888.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___378_1888.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___378_1888.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___378_1888.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___378_1888.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___378_1888.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___378_1888.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___378_1888.FStar_Tactics_Types.local_state)
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
           (let uu___379_1990 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___379_1990.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___379_1990.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___379_1990.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___379_1990.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___379_1990.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___379_1990.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___379_1990.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___379_1990.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___379_1990.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___379_1990.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___379_1990.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___379_1990.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___380_2009 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___380_2009.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___380_2009.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___380_2009.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___380_2009.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___380_2009.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___380_2009.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___380_2009.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___380_2009.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___380_2009.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___380_2009.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___380_2009.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___380_2009.FStar_Tactics_Types.local_state)
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
           (let uu___381_2205 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___381_2205.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___381_2205.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___381_2205.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___381_2205.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___381_2205.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___381_2205.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___381_2205.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___381_2205.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___381_2205.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___381_2205.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___381_2205.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___381_2205.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___382_2226 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___382_2226.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___382_2226.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___382_2226.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___382_2226.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___382_2226.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___382_2226.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___382_2226.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___382_2226.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___382_2226.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___382_2226.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___382_2226.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___382_2226.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___383_2247 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___383_2247.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___383_2247.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___383_2247.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___383_2247.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___383_2247.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___383_2247.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___383_2247.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___383_2247.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___383_2247.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___383_2247.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___383_2247.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___383_2247.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___384_2268 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___384_2268.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___384_2268.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___384_2268.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___384_2268.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___384_2268.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___384_2268.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___384_2268.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___384_2268.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___384_2268.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___384_2268.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___384_2268.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___384_2268.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2280  -> add_goals [g]) 
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
        let uu____2311 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____2311 with
        | (u,ctx_uvar,g_u) ->
            let uu____2345 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2345
              (fun uu____2354  ->
                 let uu____2355 =
                   let uu____2360 =
                     let uu____2361 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2361  in
                   (u, uu____2360)  in
                 ret uu____2355)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2381 = FStar_Syntax_Util.un_squash t  in
    match uu____2381 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2392 =
          let uu____2393 = FStar_Syntax_Subst.compress t'  in
          uu____2393.FStar_Syntax_Syntax.n  in
        (match uu____2392 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2398 -> false)
    | uu____2400 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2413 = FStar_Syntax_Util.un_squash t  in
    match uu____2413 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2424 =
          let uu____2425 = FStar_Syntax_Subst.compress t'  in
          uu____2425.FStar_Syntax_Syntax.n  in
        (match uu____2424 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2430 -> false)
    | uu____2432 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2445  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2457 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2457 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2464 = goal_to_string_verbose hd1  in
                    let uu____2466 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2464 uu____2466);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2479 =
      bind get
        (fun ps  ->
           let uu____2485 = cur_goal ()  in
           bind uu____2485
             (fun g  ->
                (let uu____2492 =
                   let uu____2493 = FStar_Tactics_Types.goal_type g  in
                   uu____2493.FStar_Syntax_Syntax.pos  in
                 let uu____2496 =
                   let uu____2502 =
                     let uu____2504 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2504
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2502)  in
                 FStar_Errors.log_issue uu____2492 uu____2496);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2479
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2527  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___385_2538 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___385_2538.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___385_2538.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___385_2538.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___385_2538.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___385_2538.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___385_2538.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___385_2538.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___385_2538.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___385_2538.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___385_2538.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___385_2538.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___385_2538.FStar_Tactics_Types.local_state)
           }  in
         let uu____2540 = set ps1  in
         bind uu____2540
           (fun uu____2545  ->
              let uu____2546 = FStar_BigInt.of_int_fs n1  in ret uu____2546))
  
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
              let uu____2584 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2584 phi  in
            let uu____2585 = new_uvar reason env typ  in
            bind uu____2585
              (fun uu____2600  ->
                 match uu____2600 with
                 | (uu____2607,ctx_uvar) ->
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
             (fun uu____2654  ->
                let uu____2655 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2655)
             (fun uu____2660  ->
                let e1 =
                  let uu___386_2662 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___386_2662.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___386_2662.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___386_2662.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___386_2662.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___386_2662.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___386_2662.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___386_2662.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___386_2662.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___386_2662.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___386_2662.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___386_2662.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___386_2662.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___386_2662.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___386_2662.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___386_2662.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___386_2662.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___386_2662.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___386_2662.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___386_2662.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___386_2662.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___386_2662.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___386_2662.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___386_2662.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___386_2662.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___386_2662.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___386_2662.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___386_2662.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___386_2662.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___386_2662.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___386_2662.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___386_2662.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___386_2662.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___386_2662.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___386_2662.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___386_2662.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___386_2662.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___386_2662.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___386_2662.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___386_2662.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___386_2662.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___386_2662.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___386_2662.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___388_2674  ->
                     match () with
                     | () ->
                         let uu____2683 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2683) ()
                with
                | FStar_Errors.Err (uu____2710,msg) ->
                    let uu____2714 = tts e1 t  in
                    let uu____2716 =
                      let uu____2718 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2718
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2714 uu____2716 msg
                | FStar_Errors.Error (uu____2728,msg,uu____2730) ->
                    let uu____2733 = tts e1 t  in
                    let uu____2735 =
                      let uu____2737 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2737
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2733 uu____2735 msg))
  
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
             (fun uu____2790  ->
                let uu____2791 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2791)
             (fun uu____2796  ->
                let e1 =
                  let uu___389_2798 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___389_2798.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___389_2798.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___389_2798.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___389_2798.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___389_2798.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___389_2798.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___389_2798.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___389_2798.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___389_2798.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___389_2798.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___389_2798.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___389_2798.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___389_2798.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___389_2798.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___389_2798.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___389_2798.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___389_2798.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___389_2798.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___389_2798.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___389_2798.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___389_2798.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___389_2798.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___389_2798.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___389_2798.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___389_2798.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___389_2798.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___389_2798.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___389_2798.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___389_2798.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___389_2798.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___389_2798.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___389_2798.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___389_2798.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___389_2798.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___389_2798.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___389_2798.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___389_2798.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___389_2798.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___389_2798.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___389_2798.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___389_2798.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___389_2798.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___391_2813  ->
                     match () with
                     | () ->
                         let uu____2822 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2822 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2860,msg) ->
                    let uu____2864 = tts e1 t  in
                    let uu____2866 =
                      let uu____2868 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2868
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2864 uu____2866 msg
                | FStar_Errors.Error (uu____2878,msg,uu____2880) ->
                    let uu____2883 = tts e1 t  in
                    let uu____2885 =
                      let uu____2887 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2887
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2883 uu____2885 msg))
  
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
             (fun uu____2940  ->
                let uu____2941 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2941)
             (fun uu____2947  ->
                let e1 =
                  let uu___392_2949 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___392_2949.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___392_2949.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___392_2949.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___392_2949.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___392_2949.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___392_2949.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___392_2949.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___392_2949.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___392_2949.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___392_2949.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___392_2949.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___392_2949.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___392_2949.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___392_2949.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___392_2949.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___392_2949.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___392_2949.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___392_2949.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___392_2949.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___392_2949.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___392_2949.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___392_2949.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___392_2949.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___392_2949.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___392_2949.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___392_2949.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___392_2949.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___392_2949.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___392_2949.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___392_2949.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___392_2949.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___392_2949.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___392_2949.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___392_2949.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___392_2949.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___392_2949.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___392_2949.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___392_2949.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___392_2949.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___392_2949.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___392_2949.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___392_2949.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___393_2952 = e1  in
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
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___393_2952.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___393_2952.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___393_2952.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___393_2952.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___393_2952.FStar_TypeChecker_Env.uvar_subtyping);
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
                try
                  (fun uu___395_2967  ->
                     match () with
                     | () ->
                         let uu____2976 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2976 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3014,msg) ->
                    let uu____3018 = tts e2 t  in
                    let uu____3020 =
                      let uu____3022 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3022
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3018 uu____3020 msg
                | FStar_Errors.Error (uu____3032,msg,uu____3034) ->
                    let uu____3037 = tts e2 t  in
                    let uu____3039 =
                      let uu____3041 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3041
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3037 uu____3039 msg))
  
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
  fun uu____3075  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___396_3094 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___396_3094.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___396_3094.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___396_3094.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___396_3094.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___396_3094.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___396_3094.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___396_3094.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___396_3094.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___396_3094.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___396_3094.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___396_3094.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___396_3094.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3119 = get_guard_policy ()  in
      bind uu____3119
        (fun old_pol  ->
           let uu____3125 = set_guard_policy pol  in
           bind uu____3125
             (fun uu____3129  ->
                bind t
                  (fun r  ->
                     let uu____3133 = set_guard_policy old_pol  in
                     bind uu____3133 (fun uu____3137  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3141 = let uu____3146 = cur_goal ()  in trytac uu____3146  in
  bind uu____3141
    (fun uu___359_3153  ->
       match uu___359_3153 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3159 = FStar_Options.peek ()  in ret uu____3159)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3184  ->
             let uu____3185 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3185)
          (fun uu____3190  ->
             let uu____3191 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3191
               (fun uu____3195  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3199 =
                         let uu____3200 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3200.FStar_TypeChecker_Env.guard_f  in
                       match uu____3199 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3204 = istrivial e f  in
                           if uu____3204
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3217 =
                                          let uu____3223 =
                                            let uu____3225 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3225
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3223)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3217);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3231  ->
                                           let uu____3232 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3232)
                                        (fun uu____3237  ->
                                           let uu____3238 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3238
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___397_3246 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___397_3246.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___397_3246.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___397_3246.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___397_3246.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3250  ->
                                           let uu____3251 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3251)
                                        (fun uu____3256  ->
                                           let uu____3257 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3257
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___398_3265 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___398_3265.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___398_3265.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___398_3265.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___398_3265.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3269  ->
                                           let uu____3270 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3270)
                                        (fun uu____3274  ->
                                           try
                                             (fun uu___400_3279  ->
                                                match () with
                                                | () ->
                                                    let uu____3282 =
                                                      let uu____3284 =
                                                        let uu____3286 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3286
                                                         in
                                                      Prims.op_Negation
                                                        uu____3284
                                                       in
                                                    if uu____3282
                                                    then
                                                      mlog
                                                        (fun uu____3293  ->
                                                           let uu____3294 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3294)
                                                        (fun uu____3298  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___399_3303 ->
                                               mlog
                                                 (fun uu____3308  ->
                                                    let uu____3309 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3309)
                                                 (fun uu____3313  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3325 =
      let uu____3328 = cur_goal ()  in
      bind uu____3328
        (fun goal  ->
           let uu____3334 =
             let uu____3343 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3343 t  in
           bind uu____3334
             (fun uu____3354  ->
                match uu____3354 with
                | (uu____3363,typ,uu____3365) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____3325
  
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
            let uu____3405 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3405 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3417  ->
    let uu____3420 = cur_goal ()  in
    bind uu____3420
      (fun goal  ->
         let uu____3426 =
           let uu____3428 = FStar_Tactics_Types.goal_env goal  in
           let uu____3429 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3428 uu____3429  in
         if uu____3426
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3435 =
              let uu____3437 = FStar_Tactics_Types.goal_env goal  in
              let uu____3438 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3437 uu____3438  in
            fail1 "Not a trivial goal: %s" uu____3435))
  
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
             let uu____3489 =
               try
                 (fun uu___405_3512  ->
                    match () with
                    | () ->
                        let uu____3523 =
                          let uu____3532 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3532
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3523) ()
               with | uu___404_3543 -> fail "divide: not enough goals"  in
             bind uu____3489
               (fun uu____3580  ->
                  match uu____3580 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___401_3606 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___401_3606.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___401_3606.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___401_3606.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___401_3606.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___401_3606.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___401_3606.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___401_3606.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___401_3606.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___401_3606.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___401_3606.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___401_3606.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3607 = set lp  in
                      bind uu____3607
                        (fun uu____3615  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___402_3631 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___402_3631.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___402_3631.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___402_3631.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___402_3631.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___402_3631.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___402_3631.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___402_3631.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___402_3631.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___402_3631.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___402_3631.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___402_3631.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3632 = set rp  in
                                     bind uu____3632
                                       (fun uu____3640  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___403_3656 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___403_3656.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___403_3656.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3657 = set p'
                                                       in
                                                    bind uu____3657
                                                      (fun uu____3665  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3671 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3693 = divide FStar_BigInt.one f idtac  in
    bind uu____3693
      (fun uu____3706  -> match uu____3706 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3744::uu____3745 ->
             let uu____3748 =
               let uu____3757 = map tau  in
               divide FStar_BigInt.one tau uu____3757  in
             bind uu____3748
               (fun uu____3775  ->
                  match uu____3775 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3817 =
        bind t1
          (fun uu____3822  ->
             let uu____3823 = map t2  in
             bind uu____3823 (fun uu____3831  -> ret ()))
         in
      focus uu____3817
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3841  ->
    let uu____3844 =
      let uu____3847 = cur_goal ()  in
      bind uu____3847
        (fun goal  ->
           let uu____3856 =
             let uu____3863 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3863  in
           match uu____3856 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3872 =
                 let uu____3874 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3874  in
               if uu____3872
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3883 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3883 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3897 = new_uvar "intro" env' typ'  in
                  bind uu____3897
                    (fun uu____3914  ->
                       match uu____3914 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3938 = set_solution goal sol  in
                           bind uu____3938
                             (fun uu____3944  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3946 =
                                  let uu____3949 = bnorm_goal g  in
                                  replace_cur uu____3949  in
                                bind uu____3946 (fun uu____3951  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3956 =
                 let uu____3958 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3959 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3958 uu____3959  in
               fail1 "goal is not an arrow (%s)" uu____3956)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3844
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3977  ->
    let uu____3984 = cur_goal ()  in
    bind uu____3984
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4003 =
            let uu____4010 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4010  in
          match uu____4003 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4023 =
                let uu____4025 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4025  in
              if uu____4023
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4042 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4042
                    in
                 let bs =
                   let uu____4053 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4053; b]  in
                 let env' =
                   let uu____4079 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4079 bs  in
                 let uu____4080 =
                   let uu____4087 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____4087  in
                 bind uu____4080
                   (fun uu____4107  ->
                      match uu____4107 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4121 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4124 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4121
                              FStar_Parser_Const.effect_Tot_lid uu____4124 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4142 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4142 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4164 =
                                   let uu____4165 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4165.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4164
                                  in
                               let uu____4181 = set_solution goal tm  in
                               bind uu____4181
                                 (fun uu____4190  ->
                                    let uu____4191 =
                                      let uu____4194 =
                                        bnorm_goal
                                          (let uu___406_4197 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___406_4197.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___406_4197.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___406_4197.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___406_4197.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4194  in
                                    bind uu____4191
                                      (fun uu____4204  ->
                                         let uu____4205 =
                                           let uu____4210 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4210, b)  in
                                         ret uu____4205)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4219 =
                let uu____4221 = FStar_Tactics_Types.goal_env goal  in
                let uu____4222 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4221 uu____4222  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4219))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4242 = cur_goal ()  in
    bind uu____4242
      (fun goal  ->
         mlog
           (fun uu____4249  ->
              let uu____4250 =
                let uu____4252 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4252  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4250)
           (fun uu____4258  ->
              let steps =
                let uu____4262 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4262
                 in
              let t =
                let uu____4266 = FStar_Tactics_Types.goal_env goal  in
                let uu____4267 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4266 uu____4267  in
              let uu____4268 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4268))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4293 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4301 -> g.FStar_Tactics_Types.opts
                 | uu____4304 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4309  ->
                    let uu____4310 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4310)
                 (fun uu____4315  ->
                    let uu____4316 = __tc_lax e t  in
                    bind uu____4316
                      (fun uu____4337  ->
                         match uu____4337 with
                         | (t1,uu____4347,uu____4348) ->
                             let steps =
                               let uu____4352 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4352
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4358  ->
                                  let uu____4359 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4359)
                               (fun uu____4363  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4293
  
let (refine_intro : unit -> unit tac) =
  fun uu____4376  ->
    let uu____4379 =
      let uu____4382 = cur_goal ()  in
      bind uu____4382
        (fun g  ->
           let uu____4389 =
             let uu____4400 = FStar_Tactics_Types.goal_env g  in
             let uu____4401 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4400 uu____4401
              in
           match uu____4389 with
           | (uu____4404,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4430 =
                 let uu____4435 =
                   let uu____4440 =
                     let uu____4441 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4441]  in
                   FStar_Syntax_Subst.open_term uu____4440 phi  in
                 match uu____4435 with
                 | (bvs,phi1) ->
                     let uu____4466 =
                       let uu____4467 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4467  in
                     (uu____4466, phi1)
                  in
               (match uu____4430 with
                | (bv1,phi1) ->
                    let uu____4486 =
                      let uu____4489 = FStar_Tactics_Types.goal_env g  in
                      let uu____4490 =
                        let uu____4491 =
                          let uu____4494 =
                            let uu____4495 =
                              let uu____4502 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4502)  in
                            FStar_Syntax_Syntax.NT uu____4495  in
                          [uu____4494]  in
                        FStar_Syntax_Subst.subst uu____4491 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4489
                        uu____4490 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4486
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4511  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4379
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4534 = cur_goal ()  in
      bind uu____4534
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4543 = FStar_Tactics_Types.goal_env goal  in
               let uu____4544 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4543 uu____4544
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4547 = __tc env t  in
           bind uu____4547
             (fun uu____4566  ->
                match uu____4566 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4581  ->
                         let uu____4582 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4584 =
                           let uu____4586 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4586
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4582 uu____4584)
                      (fun uu____4590  ->
                         let uu____4591 =
                           let uu____4594 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4594 guard  in
                         bind uu____4591
                           (fun uu____4597  ->
                              mlog
                                (fun uu____4601  ->
                                   let uu____4602 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4604 =
                                     let uu____4606 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4606
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4602 uu____4604)
                                (fun uu____4610  ->
                                   let uu____4611 =
                                     let uu____4615 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4616 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4615 typ uu____4616  in
                                   bind uu____4611
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4626 =
                                             let uu____4628 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4628 t1  in
                                           let uu____4629 =
                                             let uu____4631 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4631 typ  in
                                           let uu____4632 =
                                             let uu____4634 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4635 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4634 uu____4635  in
                                           let uu____4636 =
                                             let uu____4638 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4639 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4638 uu____4639  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4626 uu____4629 uu____4632
                                             uu____4636)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____4665 =
          mlog
            (fun uu____4670  ->
               let uu____4671 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____4671)
            (fun uu____4676  ->
               let uu____4677 =
                 let uu____4684 = __exact_now set_expected_typ1 tm  in
                 catch uu____4684  in
               bind uu____4677
                 (fun uu___361_4693  ->
                    match uu___361_4693 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4704  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4708  ->
                             let uu____4709 =
                               let uu____4716 =
                                 let uu____4719 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4719
                                   (fun uu____4724  ->
                                      let uu____4725 = refine_intro ()  in
                                      bind uu____4725
                                        (fun uu____4729  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4716  in
                             bind uu____4709
                               (fun uu___360_4736  ->
                                  match uu___360_4736 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4745  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4748  -> ret ())
                                  | FStar_Util.Inl uu____4749 ->
                                      mlog
                                        (fun uu____4751  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4754  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____4665
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4806 = f x  in
          bind uu____4806
            (fun y  ->
               let uu____4814 = mapM f xs  in
               bind uu____4814 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4886 = do_unify e ty1 ty2  in
          bind uu____4886
            (fun uu___362_4900  ->
               if uu___362_4900
               then ret acc
               else
                 (let uu____4920 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4920 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4941 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4943 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4941
                        uu____4943
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4960 =
                        let uu____4962 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4962  in
                      if uu____4960
                      then fail "Codomain is effectful"
                      else
                        (let uu____4986 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4986
                           (fun uu____5013  ->
                              match uu____5013 with
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
      let uu____5103 =
        mlog
          (fun uu____5108  ->
             let uu____5109 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5109)
          (fun uu____5114  ->
             let uu____5115 = cur_goal ()  in
             bind uu____5115
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5123 = __tc e tm  in
                  bind uu____5123
                    (fun uu____5144  ->
                       match uu____5144 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5157 =
                             let uu____5168 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5168  in
                           bind uu____5157
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5211  ->
                                       fun w  ->
                                         match uu____5211 with
                                         | (uvt,q,uu____5229) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5261 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5278  ->
                                       fun s  ->
                                         match uu____5278 with
                                         | (uu____5290,uu____5291,uv) ->
                                             let uu____5293 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5293) uvs uu____5261
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5303 = solve' goal w  in
                                bind uu____5303
                                  (fun uu____5308  ->
                                     let uu____5309 =
                                       mapM
                                         (fun uu____5326  ->
                                            match uu____5326 with
                                            | (uvt,q,uv) ->
                                                let uu____5338 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5338 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5343 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5344 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5344
                                                     then ret ()
                                                     else
                                                       (let uu____5351 =
                                                          let uu____5354 =
                                                            bnorm_goal
                                                              (let uu___407_5357
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___407_5357.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___407_5357.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___407_5357.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5354]  in
                                                        add_goals uu____5351)))
                                         uvs
                                        in
                                     bind uu____5309
                                       (fun uu____5362  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5103
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5390 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5390
    then
      let uu____5399 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5414 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5467 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5399 with
      | (pre,post) ->
          let post1 =
            let uu____5500 =
              let uu____5511 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5511]  in
            FStar_Syntax_Util.mk_app post uu____5500  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5542 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5542
       then
         let uu____5551 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5551
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____5586 =
      let uu____5589 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____5596  ->
                  let uu____5597 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____5597)
               (fun uu____5603  ->
                  let is_unit_t t =
                    let uu____5611 =
                      let uu____5612 = FStar_Syntax_Subst.compress t  in
                      uu____5612.FStar_Syntax_Syntax.n  in
                    match uu____5611 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____5618 -> false  in
                  let uu____5620 = cur_goal ()  in
                  bind uu____5620
                    (fun goal  ->
                       let uu____5626 =
                         let uu____5635 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____5635 tm  in
                       bind uu____5626
                         (fun uu____5650  ->
                            match uu____5650 with
                            | (tm1,t,guard) ->
                                let uu____5662 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____5662 with
                                 | (bs,comp) ->
                                     let uu____5695 = lemma_or_sq comp  in
                                     (match uu____5695 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____5715 =
                                            FStar_List.fold_left
                                              (fun uu____5763  ->
                                                 fun uu____5764  ->
                                                   match (uu____5763,
                                                           uu____5764)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5877 =
                                                         is_unit_t b_t  in
                                                       if uu____5877
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____5918 =
                                                            let uu____5931 =
                                                              let uu____5932
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____5932.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____5935 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____5931
                                                              uu____5935 b_t
                                                             in
                                                          match uu____5918
                                                          with
                                                          | (u,uu____5954,g_u)
                                                              ->
                                                              let uu____5968
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____5968,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____5715 with
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
                                               let uu____6047 =
                                                 let uu____6051 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____6052 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____6053 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____6051
                                                   uu____6052 uu____6053
                                                  in
                                               bind uu____6047
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____6064 =
                                                        let uu____6066 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____6066 tm1
                                                         in
                                                      let uu____6067 =
                                                        let uu____6069 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____6070 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____6069
                                                          uu____6070
                                                         in
                                                      let uu____6071 =
                                                        let uu____6073 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____6074 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____6073
                                                          uu____6074
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____6064 uu____6067
                                                        uu____6071
                                                    else
                                                      (let uu____6078 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____6078
                                                         (fun uu____6083  ->
                                                            let uu____6084 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____6084
                                                              (fun uu____6092
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____6118
                                                                    =
                                                                    let uu____6121
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6121
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6118
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
                                                                    let uu____6157
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6157)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____6174
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____6174
                                                                   with
                                                                   | 
                                                                   (hd1,uu____6193)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6220)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6237
                                                                    -> false)
                                                                    in
                                                                 let uu____6239
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
                                                                    let uu____6269
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____6269
                                                                    with
                                                                    | 
                                                                    (hd1,uu____6291)
                                                                    ->
                                                                    let uu____6316
                                                                    =
                                                                    let uu____6317
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____6317.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____6316
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____6325)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___408_6345
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___408_6345.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___408_6345.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___408_6345.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___408_6345.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____6348
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____6354
                                                                     ->
                                                                    let uu____6355
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____6357
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____6355
                                                                    uu____6357)
                                                                    (fun
                                                                    uu____6364
                                                                     ->
                                                                    let env =
                                                                    let uu___409_6366
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___409_6366.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____6369
                                                                    =
                                                                    let uu____6372
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____6376
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____6378
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____6376
                                                                    uu____6378
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____6384
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____6372
                                                                    uu____6384
                                                                    g_typ  in
                                                                    bind
                                                                    uu____6369
                                                                    (fun
                                                                    uu____6388
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____6239
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
                                                                    let uu____6452
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____6452
                                                                    then
                                                                    let uu____6457
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____6457
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
                                                                    let uu____6472
                                                                    =
                                                                    let uu____6474
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____6474
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____6472)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____6475
                                                                    =
                                                                    let uu____6478
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____6478
                                                                    guard  in
                                                                    bind
                                                                    uu____6475
                                                                    (fun
                                                                    uu____6482
                                                                     ->
                                                                    let uu____6483
                                                                    =
                                                                    let uu____6486
                                                                    =
                                                                    let uu____6488
                                                                    =
                                                                    let uu____6490
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6491
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____6490
                                                                    uu____6491
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____6488
                                                                     in
                                                                    if
                                                                    uu____6486
                                                                    then
                                                                    let uu____6495
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____6495
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____6483
                                                                    (fun
                                                                    uu____6500
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____5589  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____5586
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____6524 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____6524 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____6534::(e1,uu____6536)::(e2,uu____6538)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____6599 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____6624 = destruct_eq' typ  in
    match uu____6624 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____6654 = FStar_Syntax_Util.un_squash typ  in
        (match uu____6654 with
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
        let uu____6723 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____6723 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____6781 = aux e'  in
               FStar_Util.map_opt uu____6781
                 (fun uu____6812  ->
                    match uu____6812 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____6838 = aux e  in
      FStar_Util.map_opt uu____6838
        (fun uu____6869  ->
           match uu____6869 with
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
          let uu____6943 =
            let uu____6954 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____6954  in
          FStar_Util.map_opt uu____6943
            (fun uu____6972  ->
               match uu____6972 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___410_6994 = bv  in
                     let uu____6995 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___410_6994.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___410_6994.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6995
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___411_7003 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7004 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7013 =
                       let uu____7016 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7016  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___411_7003.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7004;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7013;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___411_7003.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___411_7003.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___411_7003.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___412_7017 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___412_7017.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___412_7017.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___412_7017.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___412_7017.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7028 =
      let uu____7031 = cur_goal ()  in
      bind uu____7031
        (fun goal  ->
           let uu____7039 = h  in
           match uu____7039 with
           | (bv,uu____7043) ->
               mlog
                 (fun uu____7051  ->
                    let uu____7052 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____7054 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____7052
                      uu____7054)
                 (fun uu____7059  ->
                    let uu____7060 =
                      let uu____7071 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____7071  in
                    match uu____7060 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____7098 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____7098 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____7113 =
                               let uu____7114 = FStar_Syntax_Subst.compress x
                                  in
                               uu____7114.FStar_Syntax_Syntax.n  in
                             (match uu____7113 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___413_7131 = bv2  in
                                    let uu____7132 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___413_7131.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___413_7131.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7132
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___414_7140 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____7141 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____7150 =
                                      let uu____7153 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____7153
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___414_7140.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____7141;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____7150;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___414_7140.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___414_7140.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___414_7140.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___415_7156 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___415_7156.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___415_7156.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___415_7156.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___415_7156.FStar_Tactics_Types.label)
                                     })
                              | uu____7157 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____7159 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7028
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____7189 =
        let uu____7192 = cur_goal ()  in
        bind uu____7192
          (fun goal  ->
             let uu____7203 = b  in
             match uu____7203 with
             | (bv,uu____7207) ->
                 let bv' =
                   let uu____7213 =
                     let uu___416_7214 = bv  in
                     let uu____7215 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____7215;
                       FStar_Syntax_Syntax.index =
                         (uu___416_7214.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___416_7214.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____7213  in
                 let s1 =
                   let uu____7220 =
                     let uu____7221 =
                       let uu____7228 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____7228)  in
                     FStar_Syntax_Syntax.NT uu____7221  in
                   [uu____7220]  in
                 let uu____7233 = subst_goal bv bv' s1 goal  in
                 (match uu____7233 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____7189
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____7255 =
      let uu____7258 = cur_goal ()  in
      bind uu____7258
        (fun goal  ->
           let uu____7267 = b  in
           match uu____7267 with
           | (bv,uu____7271) ->
               let uu____7276 =
                 let uu____7287 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____7287  in
               (match uu____7276 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____7314 = FStar_Syntax_Util.type_u ()  in
                    (match uu____7314 with
                     | (ty,u) ->
                         let uu____7323 = new_uvar "binder_retype" e0 ty  in
                         bind uu____7323
                           (fun uu____7342  ->
                              match uu____7342 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___417_7352 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___417_7352.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___417_7352.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____7356 =
                                      let uu____7357 =
                                        let uu____7364 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____7364)  in
                                      FStar_Syntax_Syntax.NT uu____7357  in
                                    [uu____7356]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___418_7376 = b1  in
                                         let uu____7377 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___418_7376.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___418_7376.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____7377
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____7384  ->
                                       let new_goal =
                                         let uu____7386 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____7387 =
                                           let uu____7388 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____7388
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7386 uu____7387
                                          in
                                       let uu____7389 = add_goals [new_goal]
                                          in
                                       bind uu____7389
                                         (fun uu____7394  ->
                                            let uu____7395 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____7395
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____7255
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____7421 =
        let uu____7424 = cur_goal ()  in
        bind uu____7424
          (fun goal  ->
             let uu____7433 = b  in
             match uu____7433 with
             | (bv,uu____7437) ->
                 let uu____7442 =
                   let uu____7453 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____7453  in
                 (match uu____7442 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____7483 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____7483
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___419_7488 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___419_7488.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___419_7488.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____7490 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____7490))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____7421
  
let (revert : unit -> unit tac) =
  fun uu____7503  ->
    let uu____7506 = cur_goal ()  in
    bind uu____7506
      (fun goal  ->
         let uu____7512 =
           let uu____7519 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7519  in
         match uu____7512 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____7536 =
                 let uu____7539 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____7539  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____7536
                in
             let uu____7554 = new_uvar "revert" env' typ'  in
             bind uu____7554
               (fun uu____7570  ->
                  match uu____7570 with
                  | (r,u_r) ->
                      let uu____7579 =
                        let uu____7582 =
                          let uu____7583 =
                            let uu____7584 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____7584.FStar_Syntax_Syntax.pos  in
                          let uu____7587 =
                            let uu____7592 =
                              let uu____7593 =
                                let uu____7602 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____7602  in
                              [uu____7593]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____7592  in
                          uu____7587 FStar_Pervasives_Native.None uu____7583
                           in
                        set_solution goal uu____7582  in
                      bind uu____7579
                        (fun uu____7623  ->
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
      let uu____7637 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____7637
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____7653 = cur_goal ()  in
    bind uu____7653
      (fun goal  ->
         mlog
           (fun uu____7661  ->
              let uu____7662 = FStar_Syntax_Print.binder_to_string b  in
              let uu____7664 =
                let uu____7666 =
                  let uu____7668 =
                    let uu____7677 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____7677  in
                  FStar_All.pipe_right uu____7668 FStar_List.length  in
                FStar_All.pipe_right uu____7666 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____7662 uu____7664)
           (fun uu____7698  ->
              let uu____7699 =
                let uu____7710 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____7710  in
              match uu____7699 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____7755 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____7755
                        then
                          let uu____7760 =
                            let uu____7762 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____7762
                             in
                          fail uu____7760
                        else check1 bvs2
                     in
                  let uu____7767 =
                    let uu____7769 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____7769  in
                  if uu____7767
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____7776 = check1 bvs  in
                     bind uu____7776
                       (fun uu____7782  ->
                          let env' = push_bvs e' bvs  in
                          let uu____7784 =
                            let uu____7791 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____7791  in
                          bind uu____7784
                            (fun uu____7801  ->
                               match uu____7801 with
                               | (ut,uvar_ut) ->
                                   let uu____7810 = set_solution goal ut  in
                                   bind uu____7810
                                     (fun uu____7815  ->
                                        let uu____7816 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____7816))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____7824  ->
    let uu____7827 = cur_goal ()  in
    bind uu____7827
      (fun goal  ->
         let uu____7833 =
           let uu____7840 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7840  in
         match uu____7833 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____7849) ->
             let uu____7854 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____7854)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____7867 = cur_goal ()  in
    bind uu____7867
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7877 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____7877  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7880  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____7893 = cur_goal ()  in
    bind uu____7893
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____7903 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____7903  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____7906  -> add_goals [g']))
  
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
            let uu____7947 = FStar_Syntax_Subst.compress t  in
            uu____7947.FStar_Syntax_Syntax.n  in
          let uu____7950 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___423_7957 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___423_7957.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___423_7957.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____7950
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____7974 =
                   let uu____7975 = FStar_Syntax_Subst.compress t1  in
                   uu____7975.FStar_Syntax_Syntax.n  in
                 match uu____7974 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8006 = ff hd1  in
                     bind uu____8006
                       (fun hd2  ->
                          let fa uu____8032 =
                            match uu____8032 with
                            | (a,q) ->
                                let uu____8053 = ff a  in
                                bind uu____8053 (fun a1  -> ret (a1, q))
                             in
                          let uu____8072 = mapM fa args  in
                          bind uu____8072
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____8154 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____8154 with
                      | (bs1,t') ->
                          let uu____8163 =
                            let uu____8166 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____8166 t'  in
                          bind uu____8163
                            (fun t''  ->
                               let uu____8170 =
                                 let uu____8171 =
                                   let uu____8190 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____8199 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____8190, uu____8199, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____8171  in
                               ret uu____8170))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____8274 = ff hd1  in
                     bind uu____8274
                       (fun hd2  ->
                          let ffb br =
                            let uu____8289 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____8289 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____8321 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____8321  in
                                let uu____8322 = ff1 e  in
                                bind uu____8322
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____8337 = mapM ffb brs  in
                          bind uu____8337
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____8381;
                          FStar_Syntax_Syntax.lbtyp = uu____8382;
                          FStar_Syntax_Syntax.lbeff = uu____8383;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____8385;
                          FStar_Syntax_Syntax.lbpos = uu____8386;_}::[]),e)
                     ->
                     let lb =
                       let uu____8414 =
                         let uu____8415 = FStar_Syntax_Subst.compress t1  in
                         uu____8415.FStar_Syntax_Syntax.n  in
                       match uu____8414 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____8419) -> lb
                       | uu____8435 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____8445 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8445
                         (fun def1  ->
                            ret
                              (let uu___420_8451 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___420_8451.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___420_8451.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___420_8451.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___420_8451.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___420_8451.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___420_8451.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8452 = fflb lb  in
                     bind uu____8452
                       (fun lb1  ->
                          let uu____8462 =
                            let uu____8467 =
                              let uu____8468 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____8468]  in
                            FStar_Syntax_Subst.open_term uu____8467 e  in
                          match uu____8462 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____8498 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____8498  in
                              let uu____8499 = ff1 e1  in
                              bind uu____8499
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____8546 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8546
                         (fun def  ->
                            ret
                              (let uu___421_8552 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___421_8552.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___421_8552.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___421_8552.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___421_8552.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___421_8552.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___421_8552.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8553 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____8553 with
                      | (lbs1,e1) ->
                          let uu____8568 = mapM fflb lbs1  in
                          bind uu____8568
                            (fun lbs2  ->
                               let uu____8580 = ff e1  in
                               bind uu____8580
                                 (fun e2  ->
                                    let uu____8588 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____8588 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____8659 = ff t2  in
                     bind uu____8659
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____8690 = ff t2  in
                     bind uu____8690
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____8697 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___422_8704 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___422_8704.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___422_8704.FStar_Syntax_Syntax.vars)
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
              let uu____8751 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___424_8760 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___424_8760.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___424_8760.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___424_8760.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___424_8760.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___424_8760.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___424_8760.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___424_8760.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___424_8760.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___424_8760.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___424_8760.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___424_8760.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___424_8760.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___424_8760.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___424_8760.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___424_8760.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___424_8760.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___424_8760.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___424_8760.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___424_8760.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___424_8760.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___424_8760.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___424_8760.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___424_8760.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___424_8760.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___424_8760.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___424_8760.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___424_8760.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___424_8760.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___424_8760.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___424_8760.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___424_8760.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___424_8760.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___424_8760.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___424_8760.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___424_8760.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___424_8760.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___424_8760.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___424_8760.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___424_8760.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___424_8760.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___424_8760.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___424_8760.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____8751 with
              | (t1,lcomp,g) ->
                  let uu____8767 =
                    (let uu____8771 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____8771) ||
                      (let uu____8774 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____8774)
                     in
                  if uu____8767
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____8785 = new_uvar "pointwise_rec" env typ  in
                       bind uu____8785
                         (fun uu____8802  ->
                            match uu____8802 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____8815  ->
                                      let uu____8816 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____8818 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____8816 uu____8818);
                                 (let uu____8821 =
                                    let uu____8824 =
                                      let uu____8825 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____8825 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____8824
                                      opts label1
                                     in
                                  bind uu____8821
                                    (fun uu____8829  ->
                                       let uu____8830 =
                                         bind tau
                                           (fun uu____8836  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____8842  ->
                                                   let uu____8843 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____8845 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____8843 uu____8845);
                                              ret ut1)
                                          in
                                       focus uu____8830))))
                        in
                     let uu____8848 = catch rewrite_eq  in
                     bind uu____8848
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
          let uu____9066 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____9066
            (fun t1  ->
               let uu____9074 =
                 f env
                   (let uu___427_9083 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___427_9083.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___427_9083.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____9074
                 (fun uu____9099  ->
                    match uu____9099 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____9122 =
                               let uu____9123 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____9123.FStar_Syntax_Syntax.n  in
                             match uu____9122 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____9160 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____9160
                                   (fun uu____9185  ->
                                      match uu____9185 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____9201 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____9201
                                            (fun uu____9228  ->
                                               match uu____9228 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___425_9258 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___425_9258.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___425_9258.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____9300 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____9300 with
                                  | (bs1,t') ->
                                      let uu____9315 =
                                        let uu____9322 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____9322 ctrl1 t'
                                         in
                                      bind uu____9315
                                        (fun uu____9340  ->
                                           match uu____9340 with
                                           | (t'',ctrl2) ->
                                               let uu____9355 =
                                                 let uu____9362 =
                                                   let uu___426_9365 = t4  in
                                                   let uu____9368 =
                                                     let uu____9369 =
                                                       let uu____9388 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____9397 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____9388,
                                                         uu____9397, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____9369
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____9368;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___426_9365.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___426_9365.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____9362, ctrl2)  in
                                               ret uu____9355))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____9450 -> ret (t3, ctrl1))))

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
              let uu____9497 = ctrl_tac_fold f env ctrl t  in
              bind uu____9497
                (fun uu____9521  ->
                   match uu____9521 with
                   | (t1,ctrl1) ->
                       let uu____9536 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____9536
                         (fun uu____9563  ->
                            match uu____9563 with
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
                let uu____9657 =
                  let uu____9665 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____9665
                    (fun uu____9676  ->
                       let uu____9677 = ctrl t1  in
                       bind uu____9677
                         (fun res  ->
                            let uu____9704 = trivial ()  in
                            bind uu____9704 (fun uu____9713  -> ret res)))
                   in
                bind uu____9657
                  (fun uu____9731  ->
                     match uu____9731 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____9760 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___428_9769 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___428_9769.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___428_9769.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___428_9769.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___428_9769.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___428_9769.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___428_9769.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___428_9769.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___428_9769.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___428_9769.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___428_9769.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___428_9769.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___428_9769.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___428_9769.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___428_9769.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___428_9769.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___428_9769.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___428_9769.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___428_9769.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___428_9769.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___428_9769.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___428_9769.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___428_9769.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___428_9769.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___428_9769.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___428_9769.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___428_9769.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___428_9769.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___428_9769.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___428_9769.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___428_9769.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___428_9769.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___428_9769.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___428_9769.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___428_9769.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___428_9769.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___428_9769.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___428_9769.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___428_9769.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___428_9769.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___428_9769.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___428_9769.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___428_9769.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____9760 with
                            | (t2,lcomp,g) ->
                                let uu____9780 =
                                  (let uu____9784 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____9784) ||
                                    (let uu____9787 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____9787)
                                   in
                                if uu____9780
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____9803 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____9803
                                     (fun uu____9824  ->
                                        match uu____9824 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____9841  ->
                                                  let uu____9842 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____9844 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____9842 uu____9844);
                                             (let uu____9847 =
                                                let uu____9850 =
                                                  let uu____9851 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____9851 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____9850 opts label1
                                                 in
                                              bind uu____9847
                                                (fun uu____9859  ->
                                                   let uu____9860 =
                                                     bind rewriter
                                                       (fun uu____9874  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____9880 
                                                               ->
                                                               let uu____9881
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____9883
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____9881
                                                                 uu____9883);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____9860)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____9929 =
        bind get
          (fun ps  ->
             let uu____9939 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____9939 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____9977  ->
                       let uu____9978 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____9978);
                  bind dismiss_all
                    (fun uu____9983  ->
                       let uu____9984 =
                         let uu____9991 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____9991
                           keepGoing gt1
                          in
                       bind uu____9984
                         (fun uu____10003  ->
                            match uu____10003 with
                            | (gt',uu____10011) ->
                                (log ps
                                   (fun uu____10015  ->
                                      let uu____10016 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10016);
                                 (let uu____10019 = push_goals gs  in
                                  bind uu____10019
                                    (fun uu____10024  ->
                                       let uu____10025 =
                                         let uu____10028 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10028]  in
                                       add_goals uu____10025)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____9929
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10053 =
        bind get
          (fun ps  ->
             let uu____10063 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10063 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10101  ->
                       let uu____10102 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____10102);
                  bind dismiss_all
                    (fun uu____10107  ->
                       let uu____10108 =
                         let uu____10111 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10111 gt1
                          in
                       bind uu____10108
                         (fun gt'  ->
                            log ps
                              (fun uu____10119  ->
                                 let uu____10120 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____10120);
                            (let uu____10123 = push_goals gs  in
                             bind uu____10123
                               (fun uu____10128  ->
                                  let uu____10129 =
                                    let uu____10132 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____10132]  in
                                  add_goals uu____10129))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10053
  
let (trefl : unit -> unit tac) =
  fun uu____10145  ->
    let uu____10148 =
      let uu____10151 = cur_goal ()  in
      bind uu____10151
        (fun g  ->
           let uu____10169 =
             let uu____10174 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____10174  in
           match uu____10169 with
           | FStar_Pervasives_Native.Some t ->
               let uu____10182 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____10182 with
                | (hd1,args) ->
                    let uu____10221 =
                      let uu____10234 =
                        let uu____10235 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____10235.FStar_Syntax_Syntax.n  in
                      (uu____10234, args)  in
                    (match uu____10221 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____10249::(l,uu____10251)::(r,uu____10253)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____10300 =
                           let uu____10304 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____10304 l r  in
                         bind uu____10300
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____10315 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10315 l
                                    in
                                 let r1 =
                                   let uu____10317 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10317 r
                                    in
                                 let uu____10318 =
                                   let uu____10322 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____10322 l1 r1  in
                                 bind uu____10318
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____10332 =
                                           let uu____10334 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10334 l1  in
                                         let uu____10335 =
                                           let uu____10337 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10337 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____10332 uu____10335))))
                     | (hd2,uu____10340) ->
                         let uu____10357 =
                           let uu____10359 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____10359 t  in
                         fail1 "trefl: not an equality (%s)" uu____10357))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____10148
  
let (dup : unit -> unit tac) =
  fun uu____10376  ->
    let uu____10379 = cur_goal ()  in
    bind uu____10379
      (fun g  ->
         let uu____10385 =
           let uu____10392 = FStar_Tactics_Types.goal_env g  in
           let uu____10393 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____10392 uu____10393  in
         bind uu____10385
           (fun uu____10403  ->
              match uu____10403 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___429_10413 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___429_10413.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___429_10413.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___429_10413.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___429_10413.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____10416  ->
                       let uu____10417 =
                         let uu____10420 = FStar_Tactics_Types.goal_env g  in
                         let uu____10421 =
                           let uu____10422 =
                             let uu____10423 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____10424 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____10423
                               uu____10424
                              in
                           let uu____10425 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____10426 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____10422 uu____10425 u
                             uu____10426
                            in
                         add_irrelevant_goal "dup equation" uu____10420
                           uu____10421 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____10417
                         (fun uu____10430  ->
                            let uu____10431 = add_goals [g']  in
                            bind uu____10431 (fun uu____10435  -> ret ())))))
  
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
              let uu____10561 = f x y  in
              if uu____10561 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____10584 -> (acc, l11, l21)  in
        let uu____10599 = aux [] l1 l2  in
        match uu____10599 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____10705 = get_phi g1  in
      match uu____10705 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____10712 = get_phi g2  in
          (match uu____10712 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____10725 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____10725 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____10756 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____10756 phi1  in
                    let t2 =
                      let uu____10766 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____10766 phi2  in
                    let uu____10775 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____10775
                      (fun uu____10780  ->
                         let uu____10781 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____10781
                           (fun uu____10788  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___430_10793 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____10794 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___430_10793.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___430_10793.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___430_10793.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___430_10793.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____10794;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___430_10793.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___430_10793.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___430_10793.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___430_10793.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___430_10793.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___430_10793.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___430_10793.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___430_10793.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___430_10793.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___430_10793.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___430_10793.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___430_10793.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___430_10793.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___430_10793.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___430_10793.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___430_10793.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___430_10793.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___430_10793.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___430_10793.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___430_10793.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___430_10793.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___430_10793.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___430_10793.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___430_10793.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___430_10793.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___430_10793.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___430_10793.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___430_10793.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___430_10793.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___430_10793.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___430_10793.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___430_10793.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___430_10793.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___430_10793.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___430_10793.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___430_10793.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___430_10793.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____10798 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____10798
                                (fun goal  ->
                                   mlog
                                     (fun uu____10808  ->
                                        let uu____10809 =
                                          goal_to_string_verbose g1  in
                                        let uu____10811 =
                                          goal_to_string_verbose g2  in
                                        let uu____10813 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____10809 uu____10811 uu____10813)
                                     (fun uu____10817  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____10825  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____10841 =
               set
                 (let uu___431_10846 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___431_10846.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___431_10846.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___431_10846.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___431_10846.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___431_10846.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___431_10846.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___431_10846.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___431_10846.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___431_10846.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___431_10846.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___431_10846.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___431_10846.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____10841
               (fun uu____10849  ->
                  let uu____10850 = join_goals g1 g2  in
                  bind uu____10850 (fun g12  -> add_goals [g12]))
         | uu____10855 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____10877 =
      let uu____10884 = cur_goal ()  in
      bind uu____10884
        (fun g  ->
           let uu____10894 =
             let uu____10903 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10903 t  in
           bind uu____10894
             (fun uu____10931  ->
                match uu____10931 with
                | (t1,typ,guard) ->
                    let uu____10947 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____10947 with
                     | (hd1,args) ->
                         let uu____10996 =
                           let uu____11011 =
                             let uu____11012 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____11012.FStar_Syntax_Syntax.n  in
                           (uu____11011, args)  in
                         (match uu____10996 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____11033)::(q,uu____11035)::[]) when
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
                                let uu____11089 =
                                  let uu____11090 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11090
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11089
                                 in
                              let g2 =
                                let uu____11092 =
                                  let uu____11093 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11093
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11092
                                 in
                              bind __dismiss
                                (fun uu____11100  ->
                                   let uu____11101 = add_goals [g1; g2]  in
                                   bind uu____11101
                                     (fun uu____11110  ->
                                        let uu____11111 =
                                          let uu____11116 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____11117 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____11116, uu____11117)  in
                                        ret uu____11111))
                          | uu____11122 ->
                              let uu____11137 =
                                let uu____11139 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____11139 typ  in
                              fail1 "Not a disjunction: %s" uu____11137))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____10877
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11174 =
      let uu____11177 = cur_goal ()  in
      bind uu____11177
        (fun g  ->
           FStar_Options.push ();
           (let uu____11190 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11190);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___432_11197 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___432_11197.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___432_11197.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___432_11197.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___432_11197.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11174
  
let (top_env : unit -> env tac) =
  fun uu____11214  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11229  ->
    let uu____11233 = cur_goal ()  in
    bind uu____11233
      (fun g  ->
         let uu____11240 =
           (FStar_Options.lax ()) ||
             (let uu____11243 = FStar_Tactics_Types.goal_env g  in
              uu____11243.FStar_TypeChecker_Env.lax)
            in
         ret uu____11240)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11260 =
        mlog
          (fun uu____11265  ->
             let uu____11266 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11266)
          (fun uu____11271  ->
             let uu____11272 = cur_goal ()  in
             bind uu____11272
               (fun goal  ->
                  let env =
                    let uu____11280 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11280 ty  in
                  let uu____11281 = __tc_ghost env tm  in
                  bind uu____11281
                    (fun uu____11300  ->
                       match uu____11300 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11314  ->
                                let uu____11315 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11315)
                             (fun uu____11319  ->
                                mlog
                                  (fun uu____11322  ->
                                     let uu____11323 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11323)
                                  (fun uu____11328  ->
                                     let uu____11329 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11329
                                       (fun uu____11334  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11260
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11359 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11365 =
              let uu____11372 =
                let uu____11373 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11373
                 in
              new_uvar "uvar_env.2" env uu____11372  in
            bind uu____11365
              (fun uu____11390  ->
                 match uu____11390 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11359
        (fun typ  ->
           let uu____11402 = new_uvar "uvar_env" env typ  in
           bind uu____11402
             (fun uu____11417  ->
                match uu____11417 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____11436 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____11455 -> g.FStar_Tactics_Types.opts
             | uu____11458 -> FStar_Options.peek ()  in
           let uu____11461 = FStar_Syntax_Util.head_and_args t  in
           match uu____11461 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____11481);
                FStar_Syntax_Syntax.pos = uu____11482;
                FStar_Syntax_Syntax.vars = uu____11483;_},uu____11484)
               ->
               let env1 =
                 let uu___433_11526 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___433_11526.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___433_11526.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___433_11526.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___433_11526.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___433_11526.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___433_11526.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___433_11526.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___433_11526.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___433_11526.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___433_11526.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___433_11526.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___433_11526.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___433_11526.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___433_11526.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___433_11526.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___433_11526.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___433_11526.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___433_11526.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___433_11526.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___433_11526.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___433_11526.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___433_11526.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___433_11526.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___433_11526.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___433_11526.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___433_11526.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___433_11526.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___433_11526.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___433_11526.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___433_11526.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___433_11526.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___433_11526.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___433_11526.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___433_11526.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___433_11526.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___433_11526.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___433_11526.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___433_11526.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___433_11526.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___433_11526.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___433_11526.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___433_11526.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____11530 =
                 let uu____11533 = bnorm_goal g  in [uu____11533]  in
               add_goals uu____11530
           | uu____11534 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____11436
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____11596 = if b then t2 else ret false  in
             bind uu____11596 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____11622 = trytac comp  in
      bind uu____11622
        (fun uu___363_11634  ->
           match uu___363_11634 with
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
        let uu____11676 =
          bind get
            (fun ps  ->
               let uu____11684 = __tc e t1  in
               bind uu____11684
                 (fun uu____11705  ->
                    match uu____11705 with
                    | (t11,ty1,g1) ->
                        let uu____11718 = __tc e t2  in
                        bind uu____11718
                          (fun uu____11739  ->
                             match uu____11739 with
                             | (t21,ty2,g2) ->
                                 let uu____11752 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____11752
                                   (fun uu____11759  ->
                                      let uu____11760 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____11760
                                        (fun uu____11768  ->
                                           let uu____11769 =
                                             do_unify e ty1 ty2  in
                                           let uu____11773 =
                                             do_unify e t11 t21  in
                                           tac_and uu____11769 uu____11773)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____11676
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____11821  ->
             let uu____11822 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____11822
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
        (fun uu____11856  ->
           let uu____11857 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____11857)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____11868 =
      mlog
        (fun uu____11873  ->
           let uu____11874 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____11874)
        (fun uu____11879  ->
           let uu____11880 = cur_goal ()  in
           bind uu____11880
             (fun g  ->
                let uu____11886 =
                  let uu____11895 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____11895 ty  in
                bind uu____11886
                  (fun uu____11907  ->
                     match uu____11907 with
                     | (ty1,uu____11917,guard) ->
                         let uu____11919 =
                           let uu____11922 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____11922 guard  in
                         bind uu____11919
                           (fun uu____11926  ->
                              let uu____11927 =
                                let uu____11931 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____11932 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____11931 uu____11932 ty1  in
                              bind uu____11927
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____11941 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____11941
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____11948 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____11949 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____11948
                                          uu____11949
                                         in
                                      let nty =
                                        let uu____11951 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____11951 ty1  in
                                      let uu____11952 =
                                        let uu____11956 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____11956 ng nty  in
                                      bind uu____11952
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____11965 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____11965
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____11868
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____12039 =
      let uu____12048 = cur_goal ()  in
      bind uu____12048
        (fun g  ->
           let uu____12060 =
             let uu____12069 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12069 s_tm  in
           bind uu____12060
             (fun uu____12087  ->
                match uu____12087 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12105 =
                      let uu____12108 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12108 guard  in
                    bind uu____12105
                      (fun uu____12121  ->
                         let uu____12122 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12122 with
                         | (h,args) ->
                             let uu____12167 =
                               let uu____12174 =
                                 let uu____12175 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12175.FStar_Syntax_Syntax.n  in
                               match uu____12174 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12190;
                                      FStar_Syntax_Syntax.vars = uu____12191;_},us)
                                   -> ret (fv, us)
                               | uu____12201 -> fail "type is not an fv"  in
                             bind uu____12167
                               (fun uu____12222  ->
                                  match uu____12222 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12238 =
                                        let uu____12241 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12241 t_lid
                                         in
                                      (match uu____12238 with
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
                                                  (fun uu____12292  ->
                                                     let uu____12293 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12293 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12308 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12336
                                                                  =
                                                                  let uu____12339
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12339
                                                                    c_lid
                                                                   in
                                                                match uu____12336
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
                                                                    uu____12413
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
                                                                    let uu____12418
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____12418
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____12441
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____12441
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____12484
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____12484
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____12557
                                                                    =
                                                                    let uu____12559
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____12559
                                                                     in
                                                                    failwhen
                                                                    uu____12557
                                                                    "not total?"
                                                                    (fun
                                                                    uu____12578
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
                                                                    uu___364_12595
                                                                    =
                                                                    match uu___364_12595
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____12599)
                                                                    -> true
                                                                    | 
                                                                    uu____12602
                                                                    -> false
                                                                     in
                                                                    let uu____12606
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____12606
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
                                                                    uu____12740
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
                                                                    uu____12802
                                                                     ->
                                                                    match uu____12802
                                                                    with
                                                                    | 
                                                                    ((bv,uu____12822),
                                                                    (t,uu____12824))
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
                                                                    uu____12894
                                                                     ->
                                                                    match uu____12894
                                                                    with
                                                                    | 
                                                                    ((bv,uu____12921),
                                                                    (t,uu____12923))
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
                                                                    uu____12982
                                                                     ->
                                                                    match uu____12982
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
                                                                    let uu____13037
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___434_13054
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___434_13054.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13037
                                                                    with
                                                                    | 
                                                                    (uu____13068,uu____13069,uu____13070,pat_t,uu____13072,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13079
                                                                    =
                                                                    let uu____13080
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13080
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13079
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13085
                                                                    =
                                                                    let uu____13094
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13094]
                                                                     in
                                                                    let uu____13113
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13085
                                                                    uu____13113
                                                                     in
                                                                    let nty =
                                                                    let uu____13119
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13119
                                                                     in
                                                                    let uu____13122
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13122
                                                                    (fun
                                                                    uu____13152
                                                                     ->
                                                                    match uu____13152
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
                                                                    let uu____13179
                                                                    =
                                                                    let uu____13190
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13190]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13179
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13226
                                                                    =
                                                                    let uu____13237
                                                                    =
                                                                    let uu____13242
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13242)
                                                                     in
                                                                    (g', br,
                                                                    uu____13237)
                                                                     in
                                                                    ret
                                                                    uu____13226))))))
                                                                    | 
                                                                    uu____13263
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12308
                                                           (fun goal_brs  ->
                                                              let uu____13313
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13313
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
                                                                  let uu____13386
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____13386
                                                                    (
                                                                    fun
                                                                    uu____13397
                                                                     ->
                                                                    let uu____13398
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____13398
                                                                    (fun
                                                                    uu____13408
                                                                     ->
                                                                    ret infos))))
                                            | uu____13415 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12039
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____13464::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____13494 = init xs  in x :: uu____13494
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____13507 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____13516) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____13582 = last args  in
          (match uu____13582 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____13612 =
                 let uu____13613 =
                   let uu____13618 =
                     let uu____13619 =
                       let uu____13624 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____13624  in
                     uu____13619 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____13618, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____13613  in
               FStar_All.pipe_left ret uu____13612)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____13637,uu____13638) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____13691 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____13691 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____13733 =
                      let uu____13734 =
                        let uu____13739 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____13739)  in
                      FStar_Reflection_Data.Tv_Abs uu____13734  in
                    FStar_All.pipe_left ret uu____13733))
      | FStar_Syntax_Syntax.Tm_type uu____13742 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____13767 ->
          let uu____13782 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____13782 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____13813 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____13813 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____13866 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____13879 =
            let uu____13880 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____13880  in
          FStar_All.pipe_left ret uu____13879
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____13901 =
            let uu____13902 =
              let uu____13907 =
                let uu____13908 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____13908  in
              (uu____13907, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____13902  in
          FStar_All.pipe_left ret uu____13901
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____13948 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____13953 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____13953 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14006 ->
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
             | FStar_Util.Inr uu____14048 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14052 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14052 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14072 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14078 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14133 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14133
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14154 =
                  let uu____14161 =
                    FStar_List.map
                      (fun uu____14174  ->
                         match uu____14174 with
                         | (p1,uu____14183) -> inspect_pat p1) ps
                     in
                  (fv, uu____14161)  in
                FStar_Reflection_Data.Pat_Cons uu____14154
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
              (fun uu___365_14279  ->
                 match uu___365_14279 with
                 | (pat,uu____14301,t5) ->
                     let uu____14319 = inspect_pat pat  in (uu____14319, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14328 ->
          ((let uu____14330 =
              let uu____14336 =
                let uu____14338 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14340 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14338 uu____14340
                 in
              (FStar_Errors.Warning_CantInspect, uu____14336)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14330);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____13507
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14358 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14358
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14362 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14362
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14366 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14366
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____14373 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____14373
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____14398 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____14398
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____14415 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____14415
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____14434 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____14434
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____14438 =
          let uu____14439 =
            let uu____14446 =
              let uu____14447 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____14447  in
            FStar_Syntax_Syntax.mk uu____14446  in
          uu____14439 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14438
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____14455 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14455
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14466 =
          let uu____14467 =
            let uu____14474 =
              let uu____14475 =
                let uu____14489 =
                  let uu____14492 =
                    let uu____14493 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____14493]  in
                  FStar_Syntax_Subst.close uu____14492 t2  in
                ((false, [lb]), uu____14489)  in
              FStar_Syntax_Syntax.Tm_let uu____14475  in
            FStar_Syntax_Syntax.mk uu____14474  in
          uu____14467 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14466
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14538 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____14538 with
         | (lbs,body) ->
             let uu____14553 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____14553)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____14590 =
                let uu____14591 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____14591  in
              FStar_All.pipe_left wrap uu____14590
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____14598 =
                let uu____14599 =
                  let uu____14613 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____14631 = pack_pat p1  in
                         (uu____14631, false)) ps
                     in
                  (fv, uu____14613)  in
                FStar_Syntax_Syntax.Pat_cons uu____14599  in
              FStar_All.pipe_left wrap uu____14598
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
            (fun uu___366_14680  ->
               match uu___366_14680 with
               | (pat,t1) ->
                   let uu____14697 = pack_pat pat  in
                   (uu____14697, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____14745 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14745
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____14773 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14773
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____14819 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14819
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____14858 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14858
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____14878 =
        bind get
          (fun ps  ->
             let uu____14884 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____14884 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____14878
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____14918 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___435_14925 = ps  in
                 let uu____14926 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___435_14925.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___435_14925.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___435_14925.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___435_14925.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___435_14925.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___435_14925.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___435_14925.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___435_14925.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___435_14925.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___435_14925.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___435_14925.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___435_14925.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____14926
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____14918
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____14953 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____14953 with
      | (u,ctx_uvars,g_u) ->
          let uu____14986 = FStar_List.hd ctx_uvars  in
          (match uu____14986 with
           | (ctx_uvar,uu____15000) ->
               let g =
                 let uu____15002 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15002 false
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
        let uu____15025 = goal_of_goal_ty env typ  in
        match uu____15025 with
        | (g,g_u) ->
            let ps =
              let uu____15037 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15040 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15037;
                FStar_Tactics_Types.local_state = uu____15040
              }  in
            let uu____15050 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15050)
  