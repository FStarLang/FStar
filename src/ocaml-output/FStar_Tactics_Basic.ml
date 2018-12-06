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
        (try (fun uu___367_169  -> match () with | () -> run t p) ()
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
                 let uu___368_1372 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___368_1372.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___368_1372.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___368_1372.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___368_1372.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___368_1372.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___368_1372.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___368_1372.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___368_1372.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___368_1372.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___368_1372.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___368_1372.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___368_1372.FStar_Tactics_Types.local_state)
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
           (fun uu___370_1518  ->
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
           (let uu___371_1634 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___371_1634.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___371_1634.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___371_1634.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___371_1634.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___371_1634.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___371_1634.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___371_1634.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___371_1634.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___371_1634.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___371_1634.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___371_1634.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___371_1634.FStar_Tactics_Types.local_state)
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
           (fun uu___373_1675  ->
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
         let uu___374_1756 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___374_1756.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___374_1756.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___374_1756.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___375_1759 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___375_1759.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___375_1759.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___375_1759.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___375_1759.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___375_1759.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___375_1759.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___375_1759.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___375_1759.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___375_1759.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___375_1759.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___375_1759.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___375_1759.FStar_Tactics_Types.local_state)
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
         let uu___376_1822 = ps  in
         let uu____1823 =
           FStar_List.filter
             (fun g  ->
                let uu____1829 = check_goal_solved g  in
                FStar_Option.isNone uu____1829) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___376_1822.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___376_1822.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___376_1822.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1823;
           FStar_Tactics_Types.smt_goals =
             (uu___376_1822.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___376_1822.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___376_1822.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___376_1822.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___376_1822.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___376_1822.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___376_1822.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___376_1822.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___376_1822.FStar_Tactics_Types.local_state)
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
         let uu___377_1885 = p  in
         let uu____1886 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___377_1885.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___377_1885.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___377_1885.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1886;
           FStar_Tactics_Types.smt_goals =
             (uu___377_1885.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___377_1885.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___377_1885.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___377_1885.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___377_1885.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___377_1885.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___377_1885.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___377_1885.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___377_1885.FStar_Tactics_Types.local_state)
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
           (let uu___378_1987 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___378_1987.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___378_1987.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___378_1987.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___378_1987.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___378_1987.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___378_1987.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___378_1987.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___378_1987.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___378_1987.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___378_1987.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___378_1987.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___378_1987.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___379_2006 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___379_2006.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___379_2006.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___379_2006.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___379_2006.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___379_2006.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___379_2006.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___379_2006.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___379_2006.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___379_2006.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___379_2006.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___379_2006.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___379_2006.FStar_Tactics_Types.local_state)
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
           (let uu___380_2202 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___380_2202.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___380_2202.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___380_2202.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___380_2202.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___380_2202.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___380_2202.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___380_2202.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___380_2202.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___380_2202.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___380_2202.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___380_2202.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___380_2202.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___381_2223 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___381_2223.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___381_2223.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___381_2223.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___381_2223.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___381_2223.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___381_2223.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___381_2223.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___381_2223.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___381_2223.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___381_2223.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___381_2223.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___381_2223.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___382_2244 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___382_2244.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___382_2244.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___382_2244.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___382_2244.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___382_2244.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___382_2244.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___382_2244.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___382_2244.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___382_2244.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___382_2244.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___382_2244.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___382_2244.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___383_2265 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___383_2265.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___383_2265.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___383_2265.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___383_2265.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___383_2265.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___383_2265.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___383_2265.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___383_2265.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___383_2265.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___383_2265.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___383_2265.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___383_2265.FStar_Tactics_Types.local_state)
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
    let uu____2382 = FStar_Syntax_Util.un_squash t  in
    match uu____2382 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2393 =
          let uu____2394 = FStar_Syntax_Subst.compress t'  in
          uu____2394.FStar_Syntax_Syntax.n  in
        (match uu____2393 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2399 -> false)
    | uu____2401 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2414 = FStar_Syntax_Util.un_squash t  in
    match uu____2414 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2425 =
          let uu____2426 = FStar_Syntax_Subst.compress t'  in
          uu____2426.FStar_Syntax_Syntax.n  in
        (match uu____2425 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2431 -> false)
    | uu____2433 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2446  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2458 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2458 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2465 = goal_to_string_verbose hd1  in
                    let uu____2467 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2465 uu____2467);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2480 =
      bind get
        (fun ps  ->
           let uu____2486 = cur_goal ()  in
           bind uu____2486
             (fun g  ->
                (let uu____2493 =
                   let uu____2494 = FStar_Tactics_Types.goal_type g  in
                   uu____2494.FStar_Syntax_Syntax.pos  in
                 let uu____2497 =
                   let uu____2503 =
                     let uu____2505 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2505
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2503)  in
                 FStar_Errors.log_issue uu____2493 uu____2497);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2480
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2528  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___384_2539 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___384_2539.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___384_2539.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___384_2539.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___384_2539.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___384_2539.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___384_2539.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___384_2539.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___384_2539.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___384_2539.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___384_2539.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___384_2539.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___384_2539.FStar_Tactics_Types.local_state)
           }  in
         let uu____2541 = set ps1  in
         bind uu____2541
           (fun uu____2546  ->
              let uu____2547 = FStar_BigInt.of_int_fs n1  in ret uu____2547))
  
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
              let uu____2585 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2585 phi  in
            let uu____2586 = new_uvar reason env typ  in
            bind uu____2586
              (fun uu____2601  ->
                 match uu____2601 with
                 | (uu____2608,ctx_uvar) ->
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
             (fun uu____2655  ->
                let uu____2656 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2656)
             (fun uu____2661  ->
                let e1 =
                  let uu___385_2663 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___385_2663.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___385_2663.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___385_2663.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___385_2663.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___385_2663.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___385_2663.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___385_2663.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___385_2663.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___385_2663.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___385_2663.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___385_2663.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___385_2663.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___385_2663.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___385_2663.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___385_2663.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___385_2663.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___385_2663.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___385_2663.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___385_2663.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___385_2663.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___385_2663.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___385_2663.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___385_2663.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___385_2663.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___385_2663.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___385_2663.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___385_2663.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___385_2663.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___385_2663.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___385_2663.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___385_2663.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___385_2663.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___385_2663.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___385_2663.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___385_2663.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___385_2663.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___385_2663.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___385_2663.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___385_2663.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___385_2663.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___385_2663.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___385_2663.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___387_2675  ->
                     match () with
                     | () ->
                         let uu____2684 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2684) ()
                with
                | FStar_Errors.Err (uu____2711,msg) ->
                    let uu____2715 = tts e1 t  in
                    let uu____2717 =
                      let uu____2719 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2719
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2715 uu____2717 msg
                | FStar_Errors.Error (uu____2729,msg,uu____2731) ->
                    let uu____2734 = tts e1 t  in
                    let uu____2736 =
                      let uu____2738 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2738
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2734 uu____2736 msg))
  
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
             (fun uu____2791  ->
                let uu____2792 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2792)
             (fun uu____2797  ->
                let e1 =
                  let uu___388_2799 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___388_2799.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___388_2799.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___388_2799.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___388_2799.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___388_2799.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___388_2799.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___388_2799.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___388_2799.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___388_2799.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___388_2799.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___388_2799.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___388_2799.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___388_2799.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___388_2799.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___388_2799.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___388_2799.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___388_2799.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___388_2799.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___388_2799.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___388_2799.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___388_2799.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___388_2799.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___388_2799.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___388_2799.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___388_2799.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___388_2799.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___388_2799.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___388_2799.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___388_2799.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___388_2799.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___388_2799.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___388_2799.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___388_2799.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___388_2799.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___388_2799.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___388_2799.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___388_2799.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___388_2799.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___388_2799.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___388_2799.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___388_2799.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___388_2799.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___390_2814  ->
                     match () with
                     | () ->
                         let uu____2823 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2823 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2861,msg) ->
                    let uu____2865 = tts e1 t  in
                    let uu____2867 =
                      let uu____2869 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2869
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2865 uu____2867 msg
                | FStar_Errors.Error (uu____2879,msg,uu____2881) ->
                    let uu____2884 = tts e1 t  in
                    let uu____2886 =
                      let uu____2888 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2888
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2884 uu____2886 msg))
  
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
             (fun uu____2941  ->
                let uu____2942 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2942)
             (fun uu____2948  ->
                let e1 =
                  let uu___391_2950 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___391_2950.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___391_2950.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___391_2950.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___391_2950.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___391_2950.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___391_2950.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___391_2950.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___391_2950.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___391_2950.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___391_2950.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___391_2950.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___391_2950.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___391_2950.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___391_2950.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___391_2950.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___391_2950.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___391_2950.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___391_2950.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___391_2950.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___391_2950.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___391_2950.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___391_2950.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___391_2950.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___391_2950.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___391_2950.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___391_2950.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___391_2950.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___391_2950.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___391_2950.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___391_2950.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___391_2950.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___391_2950.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___391_2950.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___391_2950.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___391_2950.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___391_2950.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___391_2950.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___391_2950.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___391_2950.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___391_2950.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___391_2950.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___391_2950.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___392_2953 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___392_2953.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___392_2953.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___392_2953.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___392_2953.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___392_2953.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___392_2953.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___392_2953.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___392_2953.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___392_2953.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___392_2953.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___392_2953.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___392_2953.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___392_2953.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___392_2953.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___392_2953.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___392_2953.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___392_2953.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___392_2953.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___392_2953.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___392_2953.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___392_2953.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___392_2953.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___392_2953.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___392_2953.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___392_2953.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___392_2953.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___392_2953.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___392_2953.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___392_2953.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___392_2953.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___392_2953.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___392_2953.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___392_2953.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___392_2953.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___392_2953.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___392_2953.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___392_2953.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___392_2953.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___392_2953.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___392_2953.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___392_2953.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___392_2953.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___394_2968  ->
                     match () with
                     | () ->
                         let uu____2977 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2977 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____3015,msg) ->
                    let uu____3019 = tts e2 t  in
                    let uu____3021 =
                      let uu____3023 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3023
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3019 uu____3021 msg
                | FStar_Errors.Error (uu____3033,msg,uu____3035) ->
                    let uu____3038 = tts e2 t  in
                    let uu____3040 =
                      let uu____3042 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3042
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3038 uu____3040 msg))
  
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
  fun uu____3076  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___395_3095 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___395_3095.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___395_3095.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___395_3095.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___395_3095.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___395_3095.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___395_3095.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___395_3095.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___395_3095.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___395_3095.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___395_3095.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___395_3095.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___395_3095.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3120 = get_guard_policy ()  in
      bind uu____3120
        (fun old_pol  ->
           let uu____3126 = set_guard_policy pol  in
           bind uu____3126
             (fun uu____3130  ->
                bind t
                  (fun r  ->
                     let uu____3134 = set_guard_policy old_pol  in
                     bind uu____3134 (fun uu____3138  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3142 = let uu____3147 = cur_goal ()  in trytac uu____3147  in
  bind uu____3142
    (fun uu___358_3154  ->
       match uu___358_3154 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3160 = FStar_Options.peek ()  in ret uu____3160)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3185  ->
             let uu____3186 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3186)
          (fun uu____3191  ->
             let uu____3192 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3192
               (fun uu____3196  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3200 =
                         let uu____3201 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3201.FStar_TypeChecker_Env.guard_f  in
                       match uu____3200 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3205 = istrivial e f  in
                           if uu____3205
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3218 =
                                          let uu____3224 =
                                            let uu____3226 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3226
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3224)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3218);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3232  ->
                                           let uu____3233 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3233)
                                        (fun uu____3238  ->
                                           let uu____3239 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3239
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___396_3247 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___396_3247.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___396_3247.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___396_3247.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___396_3247.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3251  ->
                                           let uu____3252 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3252)
                                        (fun uu____3257  ->
                                           let uu____3258 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3258
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___397_3266 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___397_3266.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___397_3266.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___397_3266.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___397_3266.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3270  ->
                                           let uu____3271 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3271)
                                        (fun uu____3275  ->
                                           try
                                             (fun uu___399_3280  ->
                                                match () with
                                                | () ->
                                                    let uu____3283 =
                                                      let uu____3285 =
                                                        let uu____3287 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3287
                                                         in
                                                      Prims.op_Negation
                                                        uu____3285
                                                       in
                                                    if uu____3283
                                                    then
                                                      mlog
                                                        (fun uu____3294  ->
                                                           let uu____3295 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3295)
                                                        (fun uu____3299  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___398_3304 ->
                                               mlog
                                                 (fun uu____3309  ->
                                                    let uu____3310 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3310)
                                                 (fun uu____3314  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3326 =
      let uu____3329 = cur_goal ()  in
      bind uu____3329
        (fun goal  ->
           let uu____3335 =
             let uu____3344 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3344 t  in
           bind uu____3335
             (fun uu____3355  ->
                match uu____3355 with
                | (uu____3364,typ,uu____3366) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____3326
  
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
            let uu____3406 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3406 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3418  ->
    let uu____3421 = cur_goal ()  in
    bind uu____3421
      (fun goal  ->
         let uu____3427 =
           let uu____3429 = FStar_Tactics_Types.goal_env goal  in
           let uu____3430 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3429 uu____3430  in
         if uu____3427
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3436 =
              let uu____3438 = FStar_Tactics_Types.goal_env goal  in
              let uu____3439 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3438 uu____3439  in
            fail1 "Not a trivial goal: %s" uu____3436))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3490 =
               try
                 (fun uu___404_3513  ->
                    match () with
                    | () ->
                        let uu____3524 =
                          let uu____3533 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3533
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3524) ()
               with | uu___403_3544 -> fail "divide: not enough goals"  in
             bind uu____3490
               (fun uu____3581  ->
                  match uu____3581 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___400_3607 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___400_3607.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___400_3607.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___400_3607.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___400_3607.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___400_3607.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___400_3607.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___400_3607.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___400_3607.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___400_3607.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___400_3607.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___400_3607.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3608 = set lp  in
                      bind uu____3608
                        (fun uu____3616  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___401_3632 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___401_3632.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___401_3632.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___401_3632.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___401_3632.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___401_3632.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___401_3632.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___401_3632.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___401_3632.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___401_3632.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___401_3632.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___401_3632.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3633 = set rp  in
                                     bind uu____3633
                                       (fun uu____3641  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___402_3657 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___402_3657.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___402_3657.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3658 = set p'
                                                       in
                                                    bind uu____3658
                                                      (fun uu____3666  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3672 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3694 = divide FStar_BigInt.one f idtac  in
    bind uu____3694
      (fun uu____3707  -> match uu____3707 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3745::uu____3746 ->
             let uu____3749 =
               let uu____3758 = map tau  in
               divide FStar_BigInt.one tau uu____3758  in
             bind uu____3749
               (fun uu____3776  ->
                  match uu____3776 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3818 =
        bind t1
          (fun uu____3823  ->
             let uu____3824 = map t2  in
             bind uu____3824 (fun uu____3832  -> ret ()))
         in
      focus uu____3818
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3842  ->
    let uu____3845 =
      let uu____3848 = cur_goal ()  in
      bind uu____3848
        (fun goal  ->
           let uu____3857 =
             let uu____3864 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3864  in
           match uu____3857 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3873 =
                 let uu____3875 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3875  in
               if uu____3873
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3884 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3884 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3898 = new_uvar "intro" env' typ'  in
                  bind uu____3898
                    (fun uu____3915  ->
                       match uu____3915 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3939 = set_solution goal sol  in
                           bind uu____3939
                             (fun uu____3945  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3947 =
                                  let uu____3950 = bnorm_goal g  in
                                  replace_cur uu____3950  in
                                bind uu____3947 (fun uu____3952  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3957 =
                 let uu____3959 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3960 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3959 uu____3960  in
               fail1 "goal is not an arrow (%s)" uu____3957)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3845
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____3978  ->
    let uu____3985 = cur_goal ()  in
    bind uu____3985
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____4004 =
            let uu____4011 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____4011  in
          match uu____4004 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4024 =
                let uu____4026 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4026  in
              if uu____4024
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4043 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4043
                    in
                 let bs =
                   let uu____4054 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4054; b]  in
                 let env' =
                   let uu____4080 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4080 bs  in
                 let uu____4081 =
                   let uu____4088 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____4088  in
                 bind uu____4081
                   (fun uu____4108  ->
                      match uu____4108 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4122 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4125 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4122
                              FStar_Parser_Const.effect_Tot_lid uu____4125 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4143 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4143 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4165 =
                                   let uu____4166 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4166.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4165
                                  in
                               let uu____4182 = set_solution goal tm  in
                               bind uu____4182
                                 (fun uu____4191  ->
                                    let uu____4192 =
                                      let uu____4195 =
                                        bnorm_goal
                                          (let uu___405_4198 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___405_4198.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___405_4198.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___405_4198.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___405_4198.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4195  in
                                    bind uu____4192
                                      (fun uu____4205  ->
                                         let uu____4206 =
                                           let uu____4211 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4211, b)  in
                                         ret uu____4206)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4220 =
                let uu____4222 = FStar_Tactics_Types.goal_env goal  in
                let uu____4223 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4222 uu____4223  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4220))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4243 = cur_goal ()  in
    bind uu____4243
      (fun goal  ->
         mlog
           (fun uu____4250  ->
              let uu____4251 =
                let uu____4253 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4253  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4251)
           (fun uu____4259  ->
              let steps =
                let uu____4263 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4263
                 in
              let t =
                let uu____4267 = FStar_Tactics_Types.goal_env goal  in
                let uu____4268 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4267 uu____4268  in
              let uu____4269 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4269))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4294 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4302 -> g.FStar_Tactics_Types.opts
                 | uu____4305 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4310  ->
                    let uu____4311 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4311)
                 (fun uu____4316  ->
                    let uu____4317 = __tc_lax e t  in
                    bind uu____4317
                      (fun uu____4338  ->
                         match uu____4338 with
                         | (t1,uu____4348,uu____4349) ->
                             let steps =
                               let uu____4353 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4353
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4359  ->
                                  let uu____4360 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4360)
                               (fun uu____4364  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4294
  
let (refine_intro : unit -> unit tac) =
  fun uu____4377  ->
    let uu____4380 =
      let uu____4383 = cur_goal ()  in
      bind uu____4383
        (fun g  ->
           let uu____4390 =
             let uu____4401 = FStar_Tactics_Types.goal_env g  in
             let uu____4402 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4401 uu____4402
              in
           match uu____4390 with
           | (uu____4405,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4431 =
                 let uu____4436 =
                   let uu____4441 =
                     let uu____4442 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4442]  in
                   FStar_Syntax_Subst.open_term uu____4441 phi  in
                 match uu____4436 with
                 | (bvs,phi1) ->
                     let uu____4467 =
                       let uu____4468 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4468  in
                     (uu____4467, phi1)
                  in
               (match uu____4431 with
                | (bv1,phi1) ->
                    let uu____4487 =
                      let uu____4490 = FStar_Tactics_Types.goal_env g  in
                      let uu____4491 =
                        let uu____4492 =
                          let uu____4495 =
                            let uu____4496 =
                              let uu____4503 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4503)  in
                            FStar_Syntax_Syntax.NT uu____4496  in
                          [uu____4495]  in
                        FStar_Syntax_Subst.subst uu____4492 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4490
                        uu____4491 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4487
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4512  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4380
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4535 = cur_goal ()  in
      bind uu____4535
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4544 = FStar_Tactics_Types.goal_env goal  in
               let uu____4545 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4544 uu____4545
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4548 = __tc env t  in
           bind uu____4548
             (fun uu____4567  ->
                match uu____4567 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4582  ->
                         let uu____4583 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4585 =
                           let uu____4587 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4587
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4583 uu____4585)
                      (fun uu____4591  ->
                         let uu____4592 =
                           let uu____4595 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4595 guard  in
                         bind uu____4592
                           (fun uu____4598  ->
                              mlog
                                (fun uu____4602  ->
                                   let uu____4603 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4605 =
                                     let uu____4607 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4607
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4603 uu____4605)
                                (fun uu____4611  ->
                                   let uu____4612 =
                                     let uu____4616 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4617 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4616 typ uu____4617  in
                                   bind uu____4612
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4627 =
                                             let uu____4629 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4629 t1  in
                                           let uu____4630 =
                                             let uu____4632 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4632 typ  in
                                           let uu____4633 =
                                             let uu____4635 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4636 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4635 uu____4636  in
                                           let uu____4637 =
                                             let uu____4639 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4640 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4639 uu____4640  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4627 uu____4630 uu____4633
                                             uu____4637)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____4666 =
          mlog
            (fun uu____4671  ->
               let uu____4672 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____4672)
            (fun uu____4677  ->
               let uu____4678 =
                 let uu____4685 = __exact_now set_expected_typ1 tm  in
                 catch uu____4685  in
               bind uu____4678
                 (fun uu___360_4694  ->
                    match uu___360_4694 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4705  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4709  ->
                             let uu____4710 =
                               let uu____4717 =
                                 let uu____4720 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4720
                                   (fun uu____4725  ->
                                      let uu____4726 = refine_intro ()  in
                                      bind uu____4726
                                        (fun uu____4730  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4717  in
                             bind uu____4710
                               (fun uu___359_4737  ->
                                  match uu___359_4737 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4746  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4749  -> ret ())
                                  | FStar_Util.Inl uu____4750 ->
                                      mlog
                                        (fun uu____4752  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4755  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____4666
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4807 = f x  in
          bind uu____4807
            (fun y  ->
               let uu____4815 = mapM f xs  in
               bind uu____4815 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4887 = do_unify e ty1 ty2  in
          bind uu____4887
            (fun uu___361_4901  ->
               if uu___361_4901
               then ret acc
               else
                 (let uu____4921 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4921 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4942 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4944 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4942
                        uu____4944
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4961 =
                        let uu____4963 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4963  in
                      if uu____4961
                      then fail "Codomain is effectful"
                      else
                        (let uu____4987 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4987
                           (fun uu____5014  ->
                              match uu____5014 with
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
      let uu____5104 =
        mlog
          (fun uu____5109  ->
             let uu____5110 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5110)
          (fun uu____5115  ->
             let uu____5116 = cur_goal ()  in
             bind uu____5116
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5124 = __tc e tm  in
                  bind uu____5124
                    (fun uu____5145  ->
                       match uu____5145 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5158 =
                             let uu____5169 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5169  in
                           bind uu____5158
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5212  ->
                                       fun w  ->
                                         match uu____5212 with
                                         | (uvt,q,uu____5230) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____5262 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____5279  ->
                                       fun s  ->
                                         match uu____5279 with
                                         | (uu____5291,uu____5292,uv) ->
                                             let uu____5294 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____5294) uvs uu____5262
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____5304 = solve' goal w  in
                                bind uu____5304
                                  (fun uu____5309  ->
                                     let uu____5310 =
                                       mapM
                                         (fun uu____5327  ->
                                            match uu____5327 with
                                            | (uvt,q,uv) ->
                                                let uu____5339 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____5339 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____5344 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____5345 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____5345
                                                     then ret ()
                                                     else
                                                       (let uu____5352 =
                                                          let uu____5355 =
                                                            bnorm_goal
                                                              (let uu___406_5358
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___406_5358.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___406_5358.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___406_5358.FStar_Tactics_Types.label)
                                                               })
                                                             in
                                                          [uu____5355]  in
                                                        add_goals uu____5352)))
                                         uvs
                                        in
                                     bind uu____5310
                                       (fun uu____5363  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____5104
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____5391 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____5391
    then
      let uu____5400 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____5415 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____5468 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____5400 with
      | (pre,post) ->
          let post1 =
            let uu____5501 =
              let uu____5512 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____5512]  in
            FStar_Syntax_Util.mk_app post uu____5501  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____5543 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____5543
       then
         let uu____5552 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____5552
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
            let uu____5631 = f x e  in
            bind uu____5631 (fun e'  -> fold_left f e' xs1)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____5646 =
      let uu____5649 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____5656  ->
                  let uu____5657 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____5657)
               (fun uu____5663  ->
                  let is_unit_t t =
                    let uu____5671 =
                      let uu____5672 = FStar_Syntax_Subst.compress t  in
                      uu____5672.FStar_Syntax_Syntax.n  in
                    match uu____5671 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____5678 -> false  in
                  let uu____5680 = cur_goal ()  in
                  bind uu____5680
                    (fun goal  ->
                       let uu____5686 =
                         let uu____5695 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____5695 tm  in
                       bind uu____5686
                         (fun uu____5710  ->
                            match uu____5710 with
                            | (tm1,t,guard) ->
                                let uu____5722 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____5722 with
                                 | (bs,comp) ->
                                     let uu____5755 = lemma_or_sq comp  in
                                     (match uu____5755 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____5775 =
                                            fold_left
                                              (fun uu____5837  ->
                                                 fun uu____5838  ->
                                                   match (uu____5837,
                                                           uu____5838)
                                                   with
                                                   | ((b,aq),(uvs,imps,subst1))
                                                       ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____5989 =
                                                         is_unit_t b_t  in
                                                       if uu____5989
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
                                                         (let uu____6112 =
                                                            let uu____6119 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            new_uvar
                                                              "apply_lemma"
                                                              uu____6119 b_t
                                                             in
                                                          bind uu____6112
                                                            (fun uu____6150 
                                                               ->
                                                               match uu____6150
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
                                          bind uu____5775
                                            (fun uu____6336  ->
                                               match uu____6336 with
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
                                                   let uu____6424 =
                                                     let uu____6428 =
                                                       FStar_Tactics_Types.goal_env
                                                         goal
                                                        in
                                                     let uu____6429 =
                                                       FStar_Syntax_Util.mk_squash
                                                         FStar_Syntax_Syntax.U_zero
                                                         post1
                                                        in
                                                     let uu____6430 =
                                                       FStar_Tactics_Types.goal_type
                                                         goal
                                                        in
                                                     do_unify uu____6428
                                                       uu____6429 uu____6430
                                                      in
                                                   bind uu____6424
                                                     (fun b  ->
                                                        if
                                                          Prims.op_Negation b
                                                        then
                                                          let uu____6441 =
                                                            let uu____6443 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            tts uu____6443
                                                              tm1
                                                             in
                                                          let uu____6444 =
                                                            let uu____6446 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6447 =
                                                              FStar_Syntax_Util.mk_squash
                                                                FStar_Syntax_Syntax.U_zero
                                                                post1
                                                               in
                                                            tts uu____6446
                                                              uu____6447
                                                             in
                                                          let uu____6448 =
                                                            let uu____6450 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            let uu____6451 =
                                                              FStar_Tactics_Types.goal_type
                                                                goal
                                                               in
                                                            tts uu____6450
                                                              uu____6451
                                                             in
                                                          fail3
                                                            "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                            uu____6441
                                                            uu____6444
                                                            uu____6448
                                                        else
                                                          (let uu____6455 =
                                                             solve' goal
                                                               FStar_Syntax_Util.exp_unit
                                                              in
                                                           bind uu____6455
                                                             (fun uu____6463 
                                                                ->
                                                                let is_free_uvar
                                                                  uv t1 =
                                                                  let free_uvars
                                                                    =
                                                                    let uu____6489
                                                                    =
                                                                    let uu____6492
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____6492
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____6489
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
                                                                    let uu____6528
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____6528)
                                                                    goals
                                                                   in
                                                                let checkone
                                                                  t1 goals =
                                                                  let uu____6545
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                  match uu____6545
                                                                  with
                                                                  | (hd1,uu____6564)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____6591)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____6608
                                                                    -> false)
                                                                   in
                                                                let uu____6610
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
                                                                    let uu____6653
                                                                    = imp  in
                                                                    match uu____6653
                                                                    with
                                                                    | 
                                                                    (term,ctx_uvar)
                                                                    ->
                                                                    let uu____6664
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____6664
                                                                    with
                                                                    | 
                                                                    (hd1,uu____6686)
                                                                    ->
                                                                    let uu____6711
                                                                    =
                                                                    let uu____6712
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____6712.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____6711
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____6720)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___407_6740
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___407_6740.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___407_6740.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___407_6740.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___407_6740.FStar_Tactics_Types.label)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____6743
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____6749
                                                                     ->
                                                                    let uu____6750
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____6752
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____6750
                                                                    uu____6752)
                                                                    (fun
                                                                    uu____6759
                                                                     ->
                                                                    let env =
                                                                    let uu___408_6761
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___408_6761.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____6764
                                                                    =
                                                                    let uu____6767
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____6771
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____6773
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____6771
                                                                    uu____6773
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____6779
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____6767
                                                                    uu____6779
                                                                    g_typ  in
                                                                    bind
                                                                    uu____6764
                                                                    (fun
                                                                    uu____6783
                                                                     ->
                                                                    ret []))))))
                                                                   in
                                                                bind
                                                                  uu____6610
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
                                                                    let uu____6847
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____6847
                                                                    then
                                                                    let uu____6852
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____6852
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
                                                                    let uu____6867
                                                                    =
                                                                    let uu____6869
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____6869
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____6867)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____6870
                                                                    =
                                                                    let uu____6873
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____6873
                                                                    guard  in
                                                                    bind
                                                                    uu____6870
                                                                    (fun
                                                                    uu____6877
                                                                     ->
                                                                    let uu____6878
                                                                    =
                                                                    let uu____6881
                                                                    =
                                                                    let uu____6883
                                                                    =
                                                                    let uu____6885
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____6886
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____6885
                                                                    uu____6886
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____6883
                                                                     in
                                                                    if
                                                                    uu____6881
                                                                    then
                                                                    let uu____6890
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____6890
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    goal.FStar_Tactics_Types.label
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____6878
                                                                    (fun
                                                                    uu____6895
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____5649  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____5646
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____6919 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____6919 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____6929::(e1,uu____6931)::(e2,uu____6933)::[])) when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu____6994 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7019 = destruct_eq' typ  in
    match uu____7019 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7049 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7049 with
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
        let uu____7118 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7118 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7176 = aux e'  in
               FStar_Util.map_opt uu____7176
                 (fun uu____7207  ->
                    match uu____7207 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7233 = aux e  in
      FStar_Util.map_opt uu____7233
        (fun uu____7264  ->
           match uu____7264 with
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
          let uu____7338 =
            let uu____7349 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____7349  in
          FStar_Util.map_opt uu____7338
            (fun uu____7367  ->
               match uu____7367 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___409_7389 = bv  in
                     let uu____7390 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___409_7389.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___409_7389.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7390
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___410_7398 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7399 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7408 =
                       let uu____7411 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7411  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___410_7398.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7399;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7408;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___410_7398.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___410_7398.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___410_7398.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___410_7398.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___411_7412 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___411_7412.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___411_7412.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___411_7412.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___411_7412.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7423 =
      let uu____7426 = cur_goal ()  in
      bind uu____7426
        (fun goal  ->
           let uu____7434 = h  in
           match uu____7434 with
           | (bv,uu____7438) ->
               mlog
                 (fun uu____7446  ->
                    let uu____7447 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____7449 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____7447
                      uu____7449)
                 (fun uu____7454  ->
                    let uu____7455 =
                      let uu____7466 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____7466  in
                    match uu____7455 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____7493 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____7493 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____7508 =
                               let uu____7509 = FStar_Syntax_Subst.compress x
                                  in
                               uu____7509.FStar_Syntax_Syntax.n  in
                             (match uu____7508 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___412_7526 = bv2  in
                                    let uu____7527 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___412_7526.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___412_7526.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7527
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___413_7535 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____7536 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____7545 =
                                      let uu____7548 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____7548
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___413_7535.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____7536;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____7545;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___413_7535.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___413_7535.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___413_7535.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___413_7535.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___414_7551 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___414_7551.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___414_7551.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___414_7551.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___414_7551.FStar_Tactics_Types.label)
                                     })
                              | uu____7552 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____7554 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7423
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____7584 =
        let uu____7587 = cur_goal ()  in
        bind uu____7587
          (fun goal  ->
             let uu____7598 = b  in
             match uu____7598 with
             | (bv,uu____7602) ->
                 let bv' =
                   let uu____7608 =
                     let uu___415_7609 = bv  in
                     let uu____7610 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____7610;
                       FStar_Syntax_Syntax.index =
                         (uu___415_7609.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___415_7609.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____7608  in
                 let s1 =
                   let uu____7615 =
                     let uu____7616 =
                       let uu____7623 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____7623)  in
                     FStar_Syntax_Syntax.NT uu____7616  in
                   [uu____7615]  in
                 let uu____7628 = subst_goal bv bv' s1 goal  in
                 (match uu____7628 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____7584
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____7650 =
      let uu____7653 = cur_goal ()  in
      bind uu____7653
        (fun goal  ->
           let uu____7662 = b  in
           match uu____7662 with
           | (bv,uu____7666) ->
               let uu____7671 =
                 let uu____7682 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____7682  in
               (match uu____7671 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____7709 = FStar_Syntax_Util.type_u ()  in
                    (match uu____7709 with
                     | (ty,u) ->
                         let uu____7718 = new_uvar "binder_retype" e0 ty  in
                         bind uu____7718
                           (fun uu____7737  ->
                              match uu____7737 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___416_7747 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___416_7747.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___416_7747.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____7751 =
                                      let uu____7752 =
                                        let uu____7759 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____7759)  in
                                      FStar_Syntax_Syntax.NT uu____7752  in
                                    [uu____7751]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___417_7771 = b1  in
                                         let uu____7772 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___417_7771.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___417_7771.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____7772
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____7779  ->
                                       let new_goal =
                                         let uu____7781 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____7782 =
                                           let uu____7783 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____7783
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7781 uu____7782
                                          in
                                       let uu____7784 = add_goals [new_goal]
                                          in
                                       bind uu____7784
                                         (fun uu____7789  ->
                                            let uu____7790 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____7790
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____7650
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____7816 =
        let uu____7819 = cur_goal ()  in
        bind uu____7819
          (fun goal  ->
             let uu____7828 = b  in
             match uu____7828 with
             | (bv,uu____7832) ->
                 let uu____7837 =
                   let uu____7848 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____7848  in
                 (match uu____7837 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____7878 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____7878
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___418_7883 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___418_7883.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___418_7883.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____7885 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____7885))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____7816
  
let (revert : unit -> unit tac) =
  fun uu____7898  ->
    let uu____7901 = cur_goal ()  in
    bind uu____7901
      (fun goal  ->
         let uu____7907 =
           let uu____7914 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____7914  in
         match uu____7907 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____7931 =
                 let uu____7934 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____7934  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____7931
                in
             let uu____7949 = new_uvar "revert" env' typ'  in
             bind uu____7949
               (fun uu____7965  ->
                  match uu____7965 with
                  | (r,u_r) ->
                      let uu____7974 =
                        let uu____7977 =
                          let uu____7978 =
                            let uu____7979 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____7979.FStar_Syntax_Syntax.pos  in
                          let uu____7982 =
                            let uu____7987 =
                              let uu____7988 =
                                let uu____7997 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____7997  in
                              [uu____7988]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____7987  in
                          uu____7982 FStar_Pervasives_Native.None uu____7978
                           in
                        set_solution goal uu____7977  in
                      bind uu____7974
                        (fun uu____8018  ->
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
      let uu____8032 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8032
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8048 = cur_goal ()  in
    bind uu____8048
      (fun goal  ->
         mlog
           (fun uu____8056  ->
              let uu____8057 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8059 =
                let uu____8061 =
                  let uu____8063 =
                    let uu____8072 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8072  in
                  FStar_All.pipe_right uu____8063 FStar_List.length  in
                FStar_All.pipe_right uu____8061 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8057 uu____8059)
           (fun uu____8093  ->
              let uu____8094 =
                let uu____8105 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8105  in
              match uu____8094 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8150 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8150
                        then
                          let uu____8155 =
                            let uu____8157 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8157
                             in
                          fail uu____8155
                        else check1 bvs2
                     in
                  let uu____8162 =
                    let uu____8164 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8164  in
                  if uu____8162
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8171 = check1 bvs  in
                     bind uu____8171
                       (fun uu____8177  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8179 =
                            let uu____8186 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8186  in
                          bind uu____8179
                            (fun uu____8196  ->
                               match uu____8196 with
                               | (ut,uvar_ut) ->
                                   let uu____8205 = set_solution goal ut  in
                                   bind uu____8205
                                     (fun uu____8210  ->
                                        let uu____8211 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8211))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8219  ->
    let uu____8222 = cur_goal ()  in
    bind uu____8222
      (fun goal  ->
         let uu____8228 =
           let uu____8235 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8235  in
         match uu____8228 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8244) ->
             let uu____8249 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8249)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8262 = cur_goal ()  in
    bind uu____8262
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8272 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8272  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8275  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____8288 = cur_goal ()  in
    bind uu____8288
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8298 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8298  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8301  -> add_goals [g']))
  
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
            let uu____8342 = FStar_Syntax_Subst.compress t  in
            uu____8342.FStar_Syntax_Syntax.n  in
          let uu____8345 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___422_8352 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___422_8352.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___422_8352.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____8345
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____8369 =
                   let uu____8370 = FStar_Syntax_Subst.compress t1  in
                   uu____8370.FStar_Syntax_Syntax.n  in
                 match uu____8369 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8401 = ff hd1  in
                     bind uu____8401
                       (fun hd2  ->
                          let fa uu____8427 =
                            match uu____8427 with
                            | (a,q) ->
                                let uu____8448 = ff a  in
                                bind uu____8448 (fun a1  -> ret (a1, q))
                             in
                          let uu____8467 = mapM fa args  in
                          bind uu____8467
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____8549 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____8549 with
                      | (bs1,t') ->
                          let uu____8558 =
                            let uu____8561 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____8561 t'  in
                          bind uu____8558
                            (fun t''  ->
                               let uu____8565 =
                                 let uu____8566 =
                                   let uu____8585 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____8594 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____8585, uu____8594, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____8566  in
                               ret uu____8565))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____8669 = ff hd1  in
                     bind uu____8669
                       (fun hd2  ->
                          let ffb br =
                            let uu____8684 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____8684 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____8716 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____8716  in
                                let uu____8717 = ff1 e  in
                                bind uu____8717
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____8732 = mapM ffb brs  in
                          bind uu____8732
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____8776;
                          FStar_Syntax_Syntax.lbtyp = uu____8777;
                          FStar_Syntax_Syntax.lbeff = uu____8778;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____8780;
                          FStar_Syntax_Syntax.lbpos = uu____8781;_}::[]),e)
                     ->
                     let lb =
                       let uu____8809 =
                         let uu____8810 = FStar_Syntax_Subst.compress t1  in
                         uu____8810.FStar_Syntax_Syntax.n  in
                       match uu____8809 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____8814) -> lb
                       | uu____8830 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____8840 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8840
                         (fun def1  ->
                            ret
                              (let uu___419_8846 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___419_8846.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___419_8846.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___419_8846.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___419_8846.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___419_8846.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___419_8846.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8847 = fflb lb  in
                     bind uu____8847
                       (fun lb1  ->
                          let uu____8857 =
                            let uu____8862 =
                              let uu____8863 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____8863]  in
                            FStar_Syntax_Subst.open_term uu____8862 e  in
                          match uu____8857 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____8893 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____8893  in
                              let uu____8894 = ff1 e1  in
                              bind uu____8894
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____8941 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____8941
                         (fun def  ->
                            ret
                              (let uu___420_8947 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___420_8947.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___420_8947.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___420_8947.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___420_8947.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___420_8947.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___420_8947.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____8948 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____8948 with
                      | (lbs1,e1) ->
                          let uu____8963 = mapM fflb lbs1  in
                          bind uu____8963
                            (fun lbs2  ->
                               let uu____8975 = ff e1  in
                               bind uu____8975
                                 (fun e2  ->
                                    let uu____8983 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____8983 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9054 = ff t2  in
                     bind uu____9054
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9085 = ff t2  in
                     bind uu____9085
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9092 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___421_9099 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___421_9099.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___421_9099.FStar_Syntax_Syntax.vars)
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
              let uu____9146 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___423_9155 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___423_9155.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___423_9155.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___423_9155.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___423_9155.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___423_9155.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___423_9155.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___423_9155.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___423_9155.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___423_9155.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___423_9155.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___423_9155.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___423_9155.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___423_9155.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___423_9155.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___423_9155.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___423_9155.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___423_9155.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___423_9155.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___423_9155.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___423_9155.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___423_9155.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___423_9155.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___423_9155.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___423_9155.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___423_9155.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___423_9155.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___423_9155.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___423_9155.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___423_9155.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___423_9155.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___423_9155.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___423_9155.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___423_9155.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___423_9155.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___423_9155.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___423_9155.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___423_9155.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___423_9155.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___423_9155.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___423_9155.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___423_9155.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___423_9155.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9146 with
              | (t1,lcomp,g) ->
                  let uu____9162 =
                    (let uu____9166 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9166) ||
                      (let uu____9169 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9169)
                     in
                  if uu____9162
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9180 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9180
                         (fun uu____9197  ->
                            match uu____9197 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9210  ->
                                      let uu____9211 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9213 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9211 uu____9213);
                                 (let uu____9216 =
                                    let uu____9219 =
                                      let uu____9220 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9220 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9219
                                      opts label1
                                     in
                                  bind uu____9216
                                    (fun uu____9224  ->
                                       let uu____9225 =
                                         bind tau
                                           (fun uu____9231  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9237  ->
                                                   let uu____9238 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9240 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9238 uu____9240);
                                              ret ut1)
                                          in
                                       focus uu____9225))))
                        in
                     let uu____9243 = catch rewrite_eq  in
                     bind uu____9243
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
          let uu____9461 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____9461
            (fun t1  ->
               let uu____9469 =
                 f env
                   (let uu___426_9478 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___426_9478.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___426_9478.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____9469
                 (fun uu____9494  ->
                    match uu____9494 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____9517 =
                               let uu____9518 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____9518.FStar_Syntax_Syntax.n  in
                             match uu____9517 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____9555 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____9555
                                   (fun uu____9580  ->
                                      match uu____9580 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____9596 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____9596
                                            (fun uu____9623  ->
                                               match uu____9623 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___424_9653 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___424_9653.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___424_9653.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____9695 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____9695 with
                                  | (bs1,t') ->
                                      let uu____9710 =
                                        let uu____9717 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____9717 ctrl1 t'
                                         in
                                      bind uu____9710
                                        (fun uu____9735  ->
                                           match uu____9735 with
                                           | (t'',ctrl2) ->
                                               let uu____9750 =
                                                 let uu____9757 =
                                                   let uu___425_9760 = t4  in
                                                   let uu____9763 =
                                                     let uu____9764 =
                                                       let uu____9783 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____9792 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____9783,
                                                         uu____9792, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____9764
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____9763;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___425_9760.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___425_9760.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____9757, ctrl2)  in
                                               ret uu____9750))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____9845 -> ret (t3, ctrl1))))

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
              let uu____9892 = ctrl_tac_fold f env ctrl t  in
              bind uu____9892
                (fun uu____9916  ->
                   match uu____9916 with
                   | (t1,ctrl1) ->
                       let uu____9931 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____9931
                         (fun uu____9958  ->
                            match uu____9958 with
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
                let uu____10052 =
                  let uu____10060 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10060
                    (fun uu____10071  ->
                       let uu____10072 = ctrl t1  in
                       bind uu____10072
                         (fun res  ->
                            let uu____10099 = trivial ()  in
                            bind uu____10099 (fun uu____10108  -> ret res)))
                   in
                bind uu____10052
                  (fun uu____10126  ->
                     match uu____10126 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10155 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___427_10164 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___427_10164.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___427_10164.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___427_10164.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___427_10164.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___427_10164.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___427_10164.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___427_10164.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___427_10164.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___427_10164.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___427_10164.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___427_10164.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___427_10164.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___427_10164.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___427_10164.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___427_10164.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___427_10164.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___427_10164.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___427_10164.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___427_10164.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___427_10164.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___427_10164.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___427_10164.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___427_10164.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___427_10164.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___427_10164.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___427_10164.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___427_10164.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___427_10164.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___427_10164.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___427_10164.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___427_10164.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___427_10164.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___427_10164.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___427_10164.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___427_10164.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___427_10164.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___427_10164.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___427_10164.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___427_10164.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___427_10164.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___427_10164.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___427_10164.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10155 with
                            | (t2,lcomp,g) ->
                                let uu____10175 =
                                  (let uu____10179 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10179) ||
                                    (let uu____10182 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10182)
                                   in
                                if uu____10175
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10198 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10198
                                     (fun uu____10219  ->
                                        match uu____10219 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10236  ->
                                                  let uu____10237 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10239 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10237 uu____10239);
                                             (let uu____10242 =
                                                let uu____10245 =
                                                  let uu____10246 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10246 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10245 opts label1
                                                 in
                                              bind uu____10242
                                                (fun uu____10254  ->
                                                   let uu____10255 =
                                                     bind rewriter
                                                       (fun uu____10269  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10275 
                                                               ->
                                                               let uu____10276
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10278
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10276
                                                                 uu____10278);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10255)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____10324 =
        bind get
          (fun ps  ->
             let uu____10334 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10334 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10372  ->
                       let uu____10373 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10373);
                  bind dismiss_all
                    (fun uu____10378  ->
                       let uu____10379 =
                         let uu____10386 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10386
                           keepGoing gt1
                          in
                       bind uu____10379
                         (fun uu____10398  ->
                            match uu____10398 with
                            | (gt',uu____10406) ->
                                (log ps
                                   (fun uu____10410  ->
                                      let uu____10411 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10411);
                                 (let uu____10414 = push_goals gs  in
                                  bind uu____10414
                                    (fun uu____10419  ->
                                       let uu____10420 =
                                         let uu____10423 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10423]  in
                                       add_goals uu____10420)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10324
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10448 =
        bind get
          (fun ps  ->
             let uu____10458 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10458 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10496  ->
                       let uu____10497 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____10497);
                  bind dismiss_all
                    (fun uu____10502  ->
                       let uu____10503 =
                         let uu____10506 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10506 gt1
                          in
                       bind uu____10503
                         (fun gt'  ->
                            log ps
                              (fun uu____10514  ->
                                 let uu____10515 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____10515);
                            (let uu____10518 = push_goals gs  in
                             bind uu____10518
                               (fun uu____10523  ->
                                  let uu____10524 =
                                    let uu____10527 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____10527]  in
                                  add_goals uu____10524))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10448
  
let (trefl : unit -> unit tac) =
  fun uu____10540  ->
    let uu____10543 =
      let uu____10546 = cur_goal ()  in
      bind uu____10546
        (fun g  ->
           let uu____10564 =
             let uu____10569 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____10569  in
           match uu____10564 with
           | FStar_Pervasives_Native.Some t ->
               let uu____10577 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____10577 with
                | (hd1,args) ->
                    let uu____10616 =
                      let uu____10629 =
                        let uu____10630 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____10630.FStar_Syntax_Syntax.n  in
                      (uu____10629, args)  in
                    (match uu____10616 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____10644::(l,uu____10646)::(r,uu____10648)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____10695 =
                           let uu____10699 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____10699 l r  in
                         bind uu____10695
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____10710 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10710 l
                                    in
                                 let r1 =
                                   let uu____10712 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10712 r
                                    in
                                 let uu____10713 =
                                   let uu____10717 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____10717 l1 r1  in
                                 bind uu____10713
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____10727 =
                                           let uu____10729 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10729 l1  in
                                         let uu____10730 =
                                           let uu____10732 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10732 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____10727 uu____10730))))
                     | (hd2,uu____10735) ->
                         let uu____10752 =
                           let uu____10754 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____10754 t  in
                         fail1 "trefl: not an equality (%s)" uu____10752))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____10543
  
let (dup : unit -> unit tac) =
  fun uu____10771  ->
    let uu____10774 = cur_goal ()  in
    bind uu____10774
      (fun g  ->
         let uu____10780 =
           let uu____10787 = FStar_Tactics_Types.goal_env g  in
           let uu____10788 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____10787 uu____10788  in
         bind uu____10780
           (fun uu____10798  ->
              match uu____10798 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___428_10808 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___428_10808.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___428_10808.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___428_10808.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___428_10808.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____10811  ->
                       let uu____10812 =
                         let uu____10815 = FStar_Tactics_Types.goal_env g  in
                         let uu____10816 =
                           let uu____10817 =
                             let uu____10818 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____10819 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____10818
                               uu____10819
                              in
                           let uu____10820 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____10821 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____10817 uu____10820 u
                             uu____10821
                            in
                         add_irrelevant_goal "dup equation" uu____10815
                           uu____10816 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____10812
                         (fun uu____10825  ->
                            let uu____10826 = add_goals [g']  in
                            bind uu____10826 (fun uu____10830  -> ret ())))))
  
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
              let uu____10956 = f x y  in
              if uu____10956 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____10979 -> (acc, l11, l21)  in
        let uu____10994 = aux [] l1 l2  in
        match uu____10994 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11100 = get_phi g1  in
      match uu____11100 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11107 = get_phi g2  in
          (match uu____11107 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11120 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11120 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11151 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11151 phi1  in
                    let t2 =
                      let uu____11161 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11161 phi2  in
                    let uu____11170 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11170
                      (fun uu____11175  ->
                         let uu____11176 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11176
                           (fun uu____11183  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___429_11188 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11189 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___429_11188.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___429_11188.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___429_11188.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___429_11188.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11189;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___429_11188.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___429_11188.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___429_11188.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___429_11188.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___429_11188.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___429_11188.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___429_11188.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___429_11188.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___429_11188.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___429_11188.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___429_11188.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___429_11188.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___429_11188.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___429_11188.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___429_11188.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___429_11188.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___429_11188.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___429_11188.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___429_11188.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___429_11188.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___429_11188.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___429_11188.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___429_11188.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___429_11188.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___429_11188.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___429_11188.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___429_11188.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___429_11188.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___429_11188.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___429_11188.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___429_11188.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___429_11188.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___429_11188.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___429_11188.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___429_11188.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___429_11188.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___429_11188.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11193 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11193
                                (fun goal  ->
                                   mlog
                                     (fun uu____11203  ->
                                        let uu____11204 =
                                          goal_to_string_verbose g1  in
                                        let uu____11206 =
                                          goal_to_string_verbose g2  in
                                        let uu____11208 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11204 uu____11206 uu____11208)
                                     (fun uu____11212  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11220  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11236 =
               set
                 (let uu___430_11241 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___430_11241.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___430_11241.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___430_11241.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___430_11241.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___430_11241.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___430_11241.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___430_11241.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___430_11241.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___430_11241.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___430_11241.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___430_11241.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___430_11241.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11236
               (fun uu____11244  ->
                  let uu____11245 = join_goals g1 g2  in
                  bind uu____11245 (fun g12  -> add_goals [g12]))
         | uu____11250 -> fail "join: less than 2 goals")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) tac)
  =
  fun t  ->
    let uu____11272 =
      let uu____11279 = cur_goal ()  in
      bind uu____11279
        (fun g  ->
           let uu____11289 =
             let uu____11298 = FStar_Tactics_Types.goal_env g  in
             __tc uu____11298 t  in
           bind uu____11289
             (fun uu____11326  ->
                match uu____11326 with
                | (t1,typ,guard) ->
                    let uu____11342 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____11342 with
                     | (hd1,args) ->
                         let uu____11391 =
                           let uu____11406 =
                             let uu____11407 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____11407.FStar_Syntax_Syntax.n  in
                           (uu____11406, args)  in
                         (match uu____11391 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____11428)::(q,uu____11430)::[]) when
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
                                let uu____11484 =
                                  let uu____11485 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11485
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11484
                                 in
                              let g2 =
                                let uu____11487 =
                                  let uu____11488 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____11488
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____11487
                                 in
                              bind __dismiss
                                (fun uu____11495  ->
                                   let uu____11496 = add_goals [g1; g2]  in
                                   bind uu____11496
                                     (fun uu____11505  ->
                                        let uu____11506 =
                                          let uu____11511 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____11512 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____11511, uu____11512)  in
                                        ret uu____11506))
                          | uu____11517 ->
                              let uu____11532 =
                                let uu____11534 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____11534 typ  in
                              fail1 "Not a disjunction: %s" uu____11532))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____11272
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11569 =
      let uu____11572 = cur_goal ()  in
      bind uu____11572
        (fun g  ->
           FStar_Options.push ();
           (let uu____11585 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11585);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___431_11592 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___431_11592.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___431_11592.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___431_11592.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___431_11592.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11569
  
let (top_env : unit -> env tac) =
  fun uu____11609  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11624  ->
    let uu____11628 = cur_goal ()  in
    bind uu____11628
      (fun g  ->
         let uu____11635 =
           (FStar_Options.lax ()) ||
             (let uu____11638 = FStar_Tactics_Types.goal_env g  in
              uu____11638.FStar_TypeChecker_Env.lax)
            in
         ret uu____11635)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11655 =
        mlog
          (fun uu____11660  ->
             let uu____11661 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11661)
          (fun uu____11666  ->
             let uu____11667 = cur_goal ()  in
             bind uu____11667
               (fun goal  ->
                  let env =
                    let uu____11675 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11675 ty  in
                  let uu____11676 = __tc_ghost env tm  in
                  bind uu____11676
                    (fun uu____11695  ->
                       match uu____11695 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11709  ->
                                let uu____11710 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11710)
                             (fun uu____11714  ->
                                mlog
                                  (fun uu____11717  ->
                                     let uu____11718 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11718)
                                  (fun uu____11723  ->
                                     let uu____11724 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11724
                                       (fun uu____11729  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11655
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11754 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11760 =
              let uu____11767 =
                let uu____11768 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11768
                 in
              new_uvar "uvar_env.2" env uu____11767  in
            bind uu____11760
              (fun uu____11785  ->
                 match uu____11785 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11754
        (fun typ  ->
           let uu____11797 = new_uvar "uvar_env" env typ  in
           bind uu____11797
             (fun uu____11812  ->
                match uu____11812 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____11831 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____11850 -> g.FStar_Tactics_Types.opts
             | uu____11853 -> FStar_Options.peek ()  in
           let uu____11856 = FStar_Syntax_Util.head_and_args t  in
           match uu____11856 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____11876);
                FStar_Syntax_Syntax.pos = uu____11877;
                FStar_Syntax_Syntax.vars = uu____11878;_},uu____11879)
               ->
               let env1 =
                 let uu___432_11921 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___432_11921.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___432_11921.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___432_11921.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___432_11921.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___432_11921.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___432_11921.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___432_11921.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___432_11921.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___432_11921.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___432_11921.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___432_11921.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___432_11921.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___432_11921.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___432_11921.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___432_11921.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___432_11921.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___432_11921.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___432_11921.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___432_11921.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___432_11921.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___432_11921.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___432_11921.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___432_11921.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___432_11921.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___432_11921.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___432_11921.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___432_11921.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___432_11921.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___432_11921.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___432_11921.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___432_11921.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___432_11921.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___432_11921.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___432_11921.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___432_11921.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___432_11921.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___432_11921.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___432_11921.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___432_11921.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___432_11921.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___432_11921.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___432_11921.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____11925 =
                 let uu____11928 = bnorm_goal g  in [uu____11928]  in
               add_goals uu____11925
           | uu____11929 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____11831
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____11991 = if b then t2 else ret false  in
             bind uu____11991 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____12017 = trytac comp  in
      bind uu____12017
        (fun uu___362_12029  ->
           match uu___362_12029 with
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
        let uu____12071 =
          bind get
            (fun ps  ->
               let uu____12079 = __tc e t1  in
               bind uu____12079
                 (fun uu____12100  ->
                    match uu____12100 with
                    | (t11,ty1,g1) ->
                        let uu____12113 = __tc e t2  in
                        bind uu____12113
                          (fun uu____12134  ->
                             match uu____12134 with
                             | (t21,ty2,g2) ->
                                 let uu____12147 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12147
                                   (fun uu____12154  ->
                                      let uu____12155 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12155
                                        (fun uu____12163  ->
                                           let uu____12164 =
                                             do_unify e ty1 ty2  in
                                           let uu____12168 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12164 uu____12168)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____12071
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12216  ->
             let uu____12217 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12217
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
        (fun uu____12251  ->
           let uu____12252 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12252)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12263 =
      mlog
        (fun uu____12268  ->
           let uu____12269 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12269)
        (fun uu____12274  ->
           let uu____12275 = cur_goal ()  in
           bind uu____12275
             (fun g  ->
                let uu____12281 =
                  let uu____12290 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12290 ty  in
                bind uu____12281
                  (fun uu____12302  ->
                     match uu____12302 with
                     | (ty1,uu____12312,guard) ->
                         let uu____12314 =
                           let uu____12317 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12317 guard  in
                         bind uu____12314
                           (fun uu____12321  ->
                              let uu____12322 =
                                let uu____12326 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12327 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12326 uu____12327 ty1  in
                              bind uu____12322
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12336 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12336
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12343 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12344 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12343
                                          uu____12344
                                         in
                                      let nty =
                                        let uu____12346 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12346 ty1  in
                                      let uu____12347 =
                                        let uu____12351 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12351 ng nty  in
                                      bind uu____12347
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12360 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12360
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12263
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12434 =
      let uu____12443 = cur_goal ()  in
      bind uu____12443
        (fun g  ->
           let uu____12455 =
             let uu____12464 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12464 s_tm  in
           bind uu____12455
             (fun uu____12482  ->
                match uu____12482 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12500 =
                      let uu____12503 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12503 guard  in
                    bind uu____12500
                      (fun uu____12516  ->
                         let uu____12517 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12517 with
                         | (h,args) ->
                             let uu____12562 =
                               let uu____12569 =
                                 let uu____12570 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12570.FStar_Syntax_Syntax.n  in
                               match uu____12569 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12585;
                                      FStar_Syntax_Syntax.vars = uu____12586;_},us)
                                   -> ret (fv, us)
                               | uu____12596 -> fail "type is not an fv"  in
                             bind uu____12562
                               (fun uu____12617  ->
                                  match uu____12617 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12633 =
                                        let uu____12636 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12636 t_lid
                                         in
                                      (match uu____12633 with
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
                                                  (fun uu____12687  ->
                                                     let uu____12688 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12688 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12703 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12731
                                                                  =
                                                                  let uu____12734
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12734
                                                                    c_lid
                                                                   in
                                                                match uu____12731
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
                                                                    uu____12808
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
                                                                    let uu____12813
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____12813
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____12836
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____12836
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____12879
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____12879
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____12952
                                                                    =
                                                                    let uu____12954
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____12954
                                                                     in
                                                                    failwhen
                                                                    uu____12952
                                                                    "not total?"
                                                                    (fun
                                                                    uu____12973
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
                                                                    uu___363_12990
                                                                    =
                                                                    match uu___363_12990
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____12994)
                                                                    -> true
                                                                    | 
                                                                    uu____12997
                                                                    -> false
                                                                     in
                                                                    let uu____13001
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____13001
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
                                                                    uu____13135
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
                                                                    uu____13197
                                                                     ->
                                                                    match uu____13197
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13217),
                                                                    (t,uu____13219))
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
                                                                    uu____13289
                                                                     ->
                                                                    match uu____13289
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13316),
                                                                    (t,uu____13318))
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
                                                                    uu____13377
                                                                     ->
                                                                    match uu____13377
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
                                                                    let uu____13432
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___433_13449
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___433_13449.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13432
                                                                    with
                                                                    | 
                                                                    (uu____13463,uu____13464,uu____13465,pat_t,uu____13467,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13474
                                                                    =
                                                                    let uu____13475
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13475
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13474
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13480
                                                                    =
                                                                    let uu____13489
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13489]
                                                                     in
                                                                    let uu____13508
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13480
                                                                    uu____13508
                                                                     in
                                                                    let nty =
                                                                    let uu____13514
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13514
                                                                     in
                                                                    let uu____13517
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13517
                                                                    (fun
                                                                    uu____13547
                                                                     ->
                                                                    match uu____13547
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
                                                                    let uu____13574
                                                                    =
                                                                    let uu____13585
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13585]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13574
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13621
                                                                    =
                                                                    let uu____13632
                                                                    =
                                                                    let uu____13637
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13637)
                                                                     in
                                                                    (g', br,
                                                                    uu____13632)
                                                                     in
                                                                    ret
                                                                    uu____13621))))))
                                                                    | 
                                                                    uu____13658
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12703
                                                           (fun goal_brs  ->
                                                              let uu____13708
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13708
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
                                                                  let uu____13781
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____13781
                                                                    (
                                                                    fun
                                                                    uu____13792
                                                                     ->
                                                                    let uu____13793
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____13793
                                                                    (fun
                                                                    uu____13803
                                                                     ->
                                                                    ret infos))))
                                            | uu____13810 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12434
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____13859::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____13889 = init xs  in x :: uu____13889
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____13902 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____13911) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____13977 = last args  in
          (match uu____13977 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____14007 =
                 let uu____14008 =
                   let uu____14013 =
                     let uu____14014 =
                       let uu____14019 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____14019  in
                     uu____14014 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____14013, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____14008  in
               FStar_All.pipe_left ret uu____14007)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____14032,uu____14033) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____14086 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____14086 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____14128 =
                      let uu____14129 =
                        let uu____14134 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____14134)  in
                      FStar_Reflection_Data.Tv_Abs uu____14129  in
                    FStar_All.pipe_left ret uu____14128))
      | FStar_Syntax_Syntax.Tm_type uu____14137 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14162 ->
          let uu____14177 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14177 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14208 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14208 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14261 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14274 =
            let uu____14275 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14275  in
          FStar_All.pipe_left ret uu____14274
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14296 =
            let uu____14297 =
              let uu____14302 =
                let uu____14303 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14303  in
              (uu____14302, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14297  in
          FStar_All.pipe_left ret uu____14296
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14343 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14348 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14348 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14401 ->
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
             | FStar_Util.Inr uu____14443 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14447 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14447 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14467 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14473 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14528 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14528
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14549 =
                  let uu____14556 =
                    FStar_List.map
                      (fun uu____14569  ->
                         match uu____14569 with
                         | (p1,uu____14578) -> inspect_pat p1) ps
                     in
                  (fv, uu____14556)  in
                FStar_Reflection_Data.Pat_Cons uu____14549
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
              (fun uu___364_14674  ->
                 match uu___364_14674 with
                 | (pat,uu____14696,t5) ->
                     let uu____14714 = inspect_pat pat  in (uu____14714, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14723 ->
          ((let uu____14725 =
              let uu____14731 =
                let uu____14733 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14735 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14733 uu____14735
                 in
              (FStar_Errors.Warning_CantInspect, uu____14731)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14725);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____13902
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14753 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14753
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14757 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14757
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14761 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14761
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____14768 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____14768
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____14793 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____14793
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____14810 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____14810
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____14829 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____14829
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____14833 =
          let uu____14834 =
            let uu____14841 =
              let uu____14842 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____14842  in
            FStar_Syntax_Syntax.mk uu____14841  in
          uu____14834 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14833
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____14850 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14850
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14861 =
          let uu____14862 =
            let uu____14869 =
              let uu____14870 =
                let uu____14884 =
                  let uu____14887 =
                    let uu____14888 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____14888]  in
                  FStar_Syntax_Subst.close uu____14887 t2  in
                ((false, [lb]), uu____14884)  in
              FStar_Syntax_Syntax.Tm_let uu____14870  in
            FStar_Syntax_Syntax.mk uu____14869  in
          uu____14862 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14861
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14933 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____14933 with
         | (lbs,body) ->
             let uu____14948 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____14948)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____14985 =
                let uu____14986 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____14986  in
              FStar_All.pipe_left wrap uu____14985
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____14993 =
                let uu____14994 =
                  let uu____15008 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____15026 = pack_pat p1  in
                         (uu____15026, false)) ps
                     in
                  (fv, uu____15008)  in
                FStar_Syntax_Syntax.Pat_cons uu____14994  in
              FStar_All.pipe_left wrap uu____14993
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
            (fun uu___365_15075  ->
               match uu___365_15075 with
               | (pat,t1) ->
                   let uu____15092 = pack_pat pat  in
                   (uu____15092, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____15140 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15140
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15168 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15168
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15214 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15214
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15253 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15253
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15273 =
        bind get
          (fun ps  ->
             let uu____15279 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15279 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15273
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15313 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___434_15320 = ps  in
                 let uu____15321 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___434_15320.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___434_15320.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___434_15320.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___434_15320.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___434_15320.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___434_15320.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___434_15320.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___434_15320.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___434_15320.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___434_15320.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___434_15320.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___434_15320.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15321
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15313
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15348 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15348 with
      | (u,ctx_uvars,g_u) ->
          let uu____15381 = FStar_List.hd ctx_uvars  in
          (match uu____15381 with
           | (ctx_uvar,uu____15395) ->
               let g =
                 let uu____15397 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15397 false
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
        let uu____15420 = goal_of_goal_ty env typ  in
        match uu____15420 with
        | (g,g_u) ->
            let ps =
              let uu____15432 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15435 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15432;
                FStar_Tactics_Types.local_state = uu____15435
              }  in
            let uu____15445 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15445)
  