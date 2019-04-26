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
    let uu____44 =
      let uu____45 = FStar_Tactics_Types.goal_env g  in
      let uu____46 = FStar_Tactics_Types.goal_type g  in
      bnorm uu____45 uu____46  in
    FStar_Tactics_Types.goal_with_type g uu____44
  
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
      let uu____160 = FStar_Options.tactics_failhard ()  in
      if uu____160
      then run t p
      else
        (try (fun uu___31_170  -> match () with | () -> run t p) ()
         with
         | FStar_Errors.Err (uu____179,msg) ->
             FStar_Tactics_Result.Failed
               ((FStar_Tactics_Types.TacticFailure msg), p)
         | FStar_Errors.Error (uu____183,msg,uu____185) ->
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
           let uu____265 = run t1 p  in
           match uu____265 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____272 = t2 a  in run uu____272 q
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
    let uu____295 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____295 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____317 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____319 =
      let uu____321 = check_goal_solved g  in
      match uu____321 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____327 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____327
       in
    FStar_Util.format2 "%s%s\n" uu____317 uu____319
  
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
            let uu____374 = FStar_Options.print_implicits ()  in
            if uu____374
            then
              let uu____378 = FStar_Tactics_Types.goal_env g  in
              let uu____379 = FStar_Tactics_Types.goal_witness g  in
              tts uu____378 uu____379
            else
              (let uu____382 =
                 get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
               match uu____382 with
               | FStar_Pervasives_Native.None  -> "_"
               | FStar_Pervasives_Native.Some t ->
                   let uu____388 = FStar_Tactics_Types.goal_env g  in
                   let uu____389 = FStar_Tactics_Types.goal_witness g  in
                   tts uu____388 uu____389)
             in
          let num =
            match maybe_num with
            | FStar_Pervasives_Native.None  -> ""
            | FStar_Pervasives_Native.Some (i,n1) ->
                let uu____412 = FStar_Util.string_of_int i  in
                let uu____414 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 " %s/%s" uu____412 uu____414
             in
          let maybe_label =
            match g.FStar_Tactics_Types.label with
            | "" -> ""
            | l -> Prims.op_Hat " (" (Prims.op_Hat l ")")  in
          let actual_goal =
            if ps.FStar_Tactics_Types.tac_verb_dbg
            then goal_to_string_verbose g
            else
              (let uu____432 =
                 FStar_Syntax_Print.binders_to_string ", "
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
                  in
               let uu____435 =
                 let uu____437 = FStar_Tactics_Types.goal_env g  in
                 tts uu____437
                   (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3 "%s |- %s : %s\n" uu____432 w uu____435)
             in
          FStar_Util.format4 "%s%s%s:\n%s\n" kind num maybe_label actual_goal
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____464 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____464
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____489 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____489
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____521 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____521
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____531) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____541) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (get_phi :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g  ->
    let uu____561 =
      let uu____562 = FStar_Tactics_Types.goal_env g  in
      let uu____563 = FStar_Tactics_Types.goal_type g  in
      FStar_TypeChecker_Normalize.unfold_whnf uu____562 uu____563  in
    FStar_Syntax_Util.un_squash uu____561
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  -> let uu____572 = get_phi g  in FStar_Option.isSome uu____572 
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debugging : unit -> Prims.bool tac) =
  fun uu____596  ->
    bind get
      (fun ps  ->
         let uu____604 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac")
            in
         ret uu____604)
  
let (ps_to_string :
  (Prims.string * FStar_Tactics_Types.proofstate) -> Prims.string) =
  fun uu____619  ->
    match uu____619 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let n_active = FStar_List.length ps.FStar_Tactics_Types.goals  in
        let n_smt = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
        let n1 = n_active + n_smt  in
        let uu____641 =
          let uu____645 =
            let uu____649 =
              let uu____651 =
                FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
              FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____651
                msg
               in
            let uu____654 =
              let uu____658 =
                if
                  ps.FStar_Tactics_Types.entry_range <>
                    FStar_Range.dummyRange
                then
                  let uu____662 =
                    FStar_Range.string_of_def_range
                      ps.FStar_Tactics_Types.entry_range
                     in
                  FStar_Util.format1 "Location: %s\n" uu____662
                else ""  in
              let uu____668 =
                let uu____672 =
                  let uu____674 =
                    FStar_TypeChecker_Env.debug
                      ps.FStar_Tactics_Types.main_context
                      (FStar_Options.Other "Imp")
                     in
                  if uu____674
                  then
                    let uu____679 =
                      FStar_Common.string_of_list p_imp
                        ps.FStar_Tactics_Types.all_implicits
                       in
                    FStar_Util.format1 "Imps: %s\n" uu____679
                  else ""  in
                [uu____672]  in
              uu____658 :: uu____668  in
            uu____649 :: uu____654  in
          let uu____689 =
            let uu____693 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "Goal"
                       (FStar_Pervasives_Native.Some
                          (((Prims.parse_int "1") + i), n1)) ps g)
                ps.FStar_Tactics_Types.goals
               in
            let uu____713 =
              FStar_List.mapi
                (fun i  ->
                   fun g  ->
                     goal_to_string "SMT Goal"
                       (FStar_Pervasives_Native.Some
                          ((((Prims.parse_int "1") + n_active) + i), n1)) ps
                       g) ps.FStar_Tactics_Types.smt_goals
               in
            FStar_List.append uu____693 uu____713  in
          FStar_List.append uu____645 uu____689  in
        FStar_String.concat "" uu____641
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____743 =
        let uu____744 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____744  in
      let uu____745 =
        let uu____750 =
          let uu____751 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____751  in
        FStar_Syntax_Print.binders_to_json uu____750  in
      FStar_All.pipe_right uu____743 uu____745  in
    let uu____752 =
      let uu____760 =
        let uu____768 =
          let uu____774 =
            let uu____775 =
              let uu____783 =
                let uu____789 =
                  let uu____790 =
                    let uu____792 = FStar_Tactics_Types.goal_env g  in
                    let uu____793 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____792 uu____793  in
                  FStar_Util.JsonStr uu____790  in
                ("witness", uu____789)  in
              let uu____796 =
                let uu____804 =
                  let uu____810 =
                    let uu____811 =
                      let uu____813 = FStar_Tactics_Types.goal_env g  in
                      let uu____814 = FStar_Tactics_Types.goal_type g  in
                      tts uu____813 uu____814  in
                    FStar_Util.JsonStr uu____811  in
                  ("type", uu____810)  in
                [uu____804;
                ("label", (FStar_Util.JsonStr (g.FStar_Tactics_Types.label)))]
                 in
              uu____783 :: uu____796  in
            FStar_Util.JsonAssoc uu____775  in
          ("goal", uu____774)  in
        [uu____768]  in
      ("hyps", g_binders) :: uu____760  in
    FStar_Util.JsonAssoc uu____752
  
let (ps_to_json :
  (Prims.string * FStar_Tactics_Types.proofstate) -> FStar_Util.json) =
  fun uu____868  ->
    match uu____868 with
    | (msg,ps) ->
        let uu____878 =
          let uu____886 =
            let uu____894 =
              let uu____902 =
                let uu____910 =
                  let uu____916 =
                    let uu____917 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____917  in
                  ("goals", uu____916)  in
                let uu____922 =
                  let uu____930 =
                    let uu____936 =
                      let uu____937 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____937  in
                    ("smt-goals", uu____936)  in
                  [uu____930]  in
                uu____910 :: uu____922  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____902
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____894  in
          let uu____971 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____987 =
                let uu____993 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____993)  in
              [uu____987]
            else []  in
          FStar_List.append uu____886 uu____971  in
        FStar_Util.JsonAssoc uu____878
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____1033  ->
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
         (let uu____1064 = FStar_Tactics_Types.subst_proof_state subst1 ps
             in
          dump_proofstate uu____1064 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let traise : 'a . Prims.exn -> 'a tac =
  fun e  -> mk_tac (fun ps  -> FStar_Tactics_Result.Failed (e, ps)) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____1137 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____1137
          then dump_proofstate ps (Prims.op_Hat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed
           ((FStar_Tactics_Types.TacticFailure msg), ps))
  
let fail1 : 'Auu____1151 . Prims.string -> Prims.string -> 'Auu____1151 tac =
  fun msg  ->
    fun x  -> let uu____1168 = FStar_Util.format1 msg x  in fail uu____1168
  
let fail2 :
  'Auu____1179 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____1179 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        let uu____1203 = FStar_Util.format2 msg x y  in fail uu____1203
  
let fail3 :
  'Auu____1216 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____1216 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____1247 = FStar_Util.format3 msg x y z  in fail uu____1247
  
let fail4 :
  'Auu____1262 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____1262 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1300 = FStar_Util.format4 msg x y z w  in
            fail uu____1300
  
let catch : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1335 = run t ps  in
         match uu____1335 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___193_1359 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___193_1359.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___193_1359.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___193_1359.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___193_1359.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___193_1359.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___193_1359.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___193_1359.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___193_1359.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___193_1359.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___193_1359.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___193_1359.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___193_1359.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let recover : 'a . 'a tac -> (Prims.exn,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let uu____1398 = run t ps  in
         match uu____1398 with
         | FStar_Tactics_Result.Success (a,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inr a), q)
         | FStar_Tactics_Result.Failed (m,q) ->
             FStar_Tactics_Result.Success ((FStar_Util.Inl m), q))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1446 = catch t  in
    bind uu____1446
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1473 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try
           (fun uu___219_1505  ->
              match () with
              | () -> let uu____1510 = trytac t  in run uu____1510 ps) ()
         with
         | FStar_Errors.Err (uu____1526,msg) ->
             (log ps
                (fun uu____1532  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1538,msg,uu____1540) ->
             (log ps
                (fun uu____1545  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1582 = run t ps  in
           match uu____1582 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed
               (FStar_Tactics_Types.TacticFailure msg,q) ->
               FStar_Tactics_Result.Failed
                 ((FStar_Tactics_Types.TacticFailure
                     (Prims.op_Hat pref (Prims.op_Hat ": " msg))), q)
           | FStar_Tactics_Result.Failed (e,q) ->
               FStar_Tactics_Result.Failed (e, q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1606  -> FStar_Tactics_Result.Success ((), p)) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___254_1621 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___254_1621.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___254_1621.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___254_1621.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___254_1621.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___254_1621.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___254_1621.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___254_1621.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___254_1621.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___254_1621.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___254_1621.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___254_1621.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___254_1621.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1645 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1645
         then
           let uu____1649 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1651 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1649
             uu____1651
         else ());
        (try
           (fun uu___262_1662  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1670 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1670
                    then
                      let uu____1674 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1676 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1678 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1674
                        uu____1676 uu____1678
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1689 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1689 (fun uu____1694  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1704,msg) ->
             mlog
               (fun uu____1710  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1713  -> ret false)
         | FStar_Errors.Error (uu____1716,msg,r) ->
             mlog
               (fun uu____1724  ->
                  let uu____1725 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1725) (fun uu____1729  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___288_1743 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___288_1743.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___288_1743.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___288_1743.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___292_1746 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___292_1746.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___292_1746.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___292_1746.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___292_1746.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___292_1746.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___292_1746.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___292_1746.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___292_1746.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___292_1746.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___292_1746.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___292_1746.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___292_1746.FStar_Tactics_Types.local_state)
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
          (fun uu____1773  ->
             (let uu____1775 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1775
              then
                (FStar_Options.push ();
                 (let uu____1780 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1784 = __do_unify env t1 t2  in
              bind uu____1784
                (fun r  ->
                   (let uu____1795 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1795 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___307_1809 = ps  in
         let uu____1810 =
           FStar_List.filter
             (fun g  ->
                let uu____1816 = check_goal_solved g  in
                FStar_Option.isNone uu____1816) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___307_1809.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___307_1809.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___307_1809.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1810;
           FStar_Tactics_Types.smt_goals =
             (uu___307_1809.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___307_1809.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___307_1809.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___307_1809.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___307_1809.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___307_1809.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___307_1809.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___307_1809.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___307_1809.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1834 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1834 with
      | FStar_Pervasives_Native.Some uu____1839 ->
          let uu____1840 =
            let uu____1842 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1842  in
          fail uu____1840
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1863 = FStar_Tactics_Types.goal_env goal  in
      let uu____1864 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1863 solution uu____1864
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1871 =
         let uu___320_1872 = p  in
         let uu____1873 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___320_1872.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___320_1872.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___320_1872.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1873;
           FStar_Tactics_Types.smt_goals =
             (uu___320_1872.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___320_1872.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___320_1872.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___320_1872.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___320_1872.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___320_1872.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___320_1872.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___320_1872.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___320_1872.FStar_Tactics_Types.local_state)
         }  in
       set uu____1871)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1895  ->
           let uu____1896 =
             let uu____1898 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1898  in
           let uu____1899 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1896 uu____1899)
        (fun uu____1904  ->
           let uu____1905 = trysolve goal solution  in
           bind uu____1905
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1917  -> remove_solved_goals)
                else
                  (let uu____1920 =
                     let uu____1922 =
                       let uu____1924 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1924 solution  in
                     let uu____1925 =
                       let uu____1927 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1928 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1927 uu____1928  in
                     let uu____1929 =
                       let uu____1931 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1932 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1931 uu____1932  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1922 uu____1925 uu____1929
                      in
                   fail uu____1920)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1949 = set_solution goal solution  in
      bind uu____1949
        (fun uu____1953  ->
           bind __dismiss (fun uu____1955  -> remove_solved_goals))
  
let (set_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___336_1974 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___336_1974.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___336_1974.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___336_1974.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals = gs;
              FStar_Tactics_Types.smt_goals =
                (uu___336_1974.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___336_1974.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___336_1974.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___336_1974.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___336_1974.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___336_1974.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___336_1974.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___336_1974.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___336_1974.FStar_Tactics_Types.local_state)
            }))
  
let (set_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun ps  ->
         set
           (let uu___340_1993 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___340_1993.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___340_1993.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___340_1993.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___340_1993.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals = gs;
              FStar_Tactics_Types.depth =
                (uu___340_1993.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___340_1993.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___340_1993.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___340_1993.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___340_1993.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___340_1993.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___340_1993.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___340_1993.FStar_Tactics_Types.local_state)
            }))
  
let (dismiss_all : unit tac) = set_goals [] 
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____2009 = FStar_Options.defensive ()  in
    if uu____2009
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____2019 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____2019)
         in
      let b2 =
        b1 &&
          (let uu____2023 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____2023)
         in
      let rec aux b3 e =
        let uu____2038 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____2038 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____2058 =
        (let uu____2062 = aux b2 env  in Prims.op_Negation uu____2062) &&
          (let uu____2065 = FStar_ST.op_Bang nwarn  in
           uu____2065 < (Prims.parse_int "5"))
         in
      (if uu____2058
       then
         ((let uu____2091 =
             let uu____2092 = FStar_Tactics_Types.goal_type g  in
             uu____2092.FStar_Syntax_Syntax.pos  in
           let uu____2095 =
             let uu____2101 =
               let uu____2103 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____2103
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____2101)  in
           FStar_Errors.log_issue uu____2091 uu____2095);
          (let uu____2107 =
             let uu____2109 = FStar_ST.op_Bang nwarn  in
             uu____2109 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____2107))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___362_2178 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_2178.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_2178.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___362_2178.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___362_2178.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_2178.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_2178.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_2178.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_2178.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_2178.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_2178.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_2178.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___362_2178.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___367_2199 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_2199.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_2199.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_2199.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___367_2199.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___367_2199.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_2199.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_2199.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_2199.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_2199.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_2199.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_2199.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___367_2199.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___372_2220 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___372_2220.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___372_2220.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___372_2220.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___372_2220.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___372_2220.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___372_2220.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___372_2220.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___372_2220.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___372_2220.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___372_2220.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___372_2220.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___372_2220.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___377_2241 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___377_2241.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___377_2241.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___377_2241.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___377_2241.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___377_2241.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___377_2241.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___377_2241.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___377_2241.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___377_2241.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___377_2241.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___377_2241.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___377_2241.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____2253  -> add_goals [g]) 
let (new_uvar :
  Prims.string ->
    env ->
      FStar_Reflection_Data.typ ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____2284 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped FStar_Pervasives_Native.None
           in
        match uu____2284 with
        | (u,ctx_uvar,g_u) ->
            let uu____2322 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____2322
              (fun uu____2331  ->
                 let uu____2332 =
                   let uu____2337 =
                     let uu____2338 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____2338  in
                   (u, uu____2337)  in
                 ret uu____2332)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let uu____2359 = FStar_Syntax_Util.un_squash t1  in
    match uu____2359 with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t'  in
        let uu____2371 =
          let uu____2372 = FStar_Syntax_Subst.compress t'1  in
          uu____2372.FStar_Syntax_Syntax.n  in
        (match uu____2371 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____2377 -> false)
    | uu____2379 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____2392 = FStar_Syntax_Util.un_squash t  in
    match uu____2392 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____2403 =
          let uu____2404 = FStar_Syntax_Subst.compress t'  in
          uu____2404.FStar_Syntax_Syntax.n  in
        (match uu____2403 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____2409 -> false)
    | uu____2411 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____2424  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____2436 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____2436 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____2443 = goal_to_string_verbose hd1  in
                    let uu____2445 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____2443 uu____2445);
                   ret hd1)))
  
let (tadmit_t : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____2458 =
      bind get
        (fun ps  ->
           let uu____2464 = cur_goal ()  in
           bind uu____2464
             (fun g  ->
                (let uu____2471 =
                   let uu____2472 = FStar_Tactics_Types.goal_type g  in
                   uu____2472.FStar_Syntax_Syntax.pos  in
                 let uu____2475 =
                   let uu____2481 =
                     let uu____2483 =
                       goal_to_string "" FStar_Pervasives_Native.None ps g
                        in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____2483
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____2481)  in
                 FStar_Errors.log_issue uu____2471 uu____2475);
                solve' g t))
       in
    FStar_All.pipe_left (wrap_err "tadmit_t") uu____2458
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____2506  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___422_2517 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___422_2517.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___422_2517.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___422_2517.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___422_2517.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___422_2517.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___422_2517.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___422_2517.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___422_2517.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___422_2517.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___422_2517.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___422_2517.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___422_2517.FStar_Tactics_Types.local_state)
           }  in
         let uu____2519 = set ps1  in
         bind uu____2519
           (fun uu____2524  ->
              let uu____2525 = FStar_BigInt.of_int_fs n1  in ret uu____2525))
  
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
              let uu____2563 = env.FStar_TypeChecker_Env.universe_of env phi
                 in
              FStar_Syntax_Util.mk_squash uu____2563 phi  in
            let uu____2564 = new_uvar reason env typ  in
            bind uu____2564
              (fun uu____2579  ->
                 match uu____2579 with
                 | (uu____2586,ctx_uvar) ->
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
             (fun uu____2633  ->
                let uu____2634 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2634)
             (fun uu____2639  ->
                let e1 =
                  let uu___440_2641 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___440_2641.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___440_2641.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___440_2641.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___440_2641.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___440_2641.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___440_2641.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___440_2641.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___440_2641.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___440_2641.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___440_2641.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___440_2641.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___440_2641.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___440_2641.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___440_2641.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___440_2641.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___440_2641.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___440_2641.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___440_2641.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___440_2641.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___440_2641.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___440_2641.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___440_2641.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___440_2641.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___440_2641.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___440_2641.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___440_2641.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___440_2641.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___440_2641.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___440_2641.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___440_2641.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___440_2641.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___440_2641.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___440_2641.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___440_2641.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___440_2641.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___440_2641.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___440_2641.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___440_2641.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___440_2641.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___440_2641.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___440_2641.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___440_2641.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___444_2653  ->
                     match () with
                     | () ->
                         let uu____2662 =
                           FStar_TypeChecker_TcTerm.type_of_tot_term e1 t  in
                         ret uu____2662) ()
                with
                | FStar_Errors.Err (uu____2689,msg) ->
                    let uu____2693 = tts e1 t  in
                    let uu____2695 =
                      let uu____2697 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2697
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2693 uu____2695 msg
                | FStar_Errors.Error (uu____2707,msg,uu____2709) ->
                    let uu____2712 = tts e1 t  in
                    let uu____2714 =
                      let uu____2716 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2716
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2712 uu____2714 msg))
  
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
             (fun uu____2769  ->
                let uu____2770 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc_ghost(%s)\n" uu____2770)
             (fun uu____2775  ->
                let e1 =
                  let uu___461_2777 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___461_2777.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___461_2777.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___461_2777.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___461_2777.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___461_2777.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___461_2777.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___461_2777.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___461_2777.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___461_2777.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___461_2777.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___461_2777.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___461_2777.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___461_2777.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___461_2777.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___461_2777.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___461_2777.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___461_2777.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___461_2777.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___461_2777.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___461_2777.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___461_2777.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___461_2777.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___461_2777.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___461_2777.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___461_2777.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___461_2777.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___461_2777.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___461_2777.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___461_2777.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___461_2777.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___461_2777.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___461_2777.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___461_2777.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___461_2777.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___461_2777.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___461_2777.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___461_2777.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___461_2777.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___461_2777.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___461_2777.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___461_2777.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___461_2777.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___465_2792  ->
                     match () with
                     | () ->
                         let uu____2801 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e1 t
                            in
                         (match uu____2801 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2839,msg) ->
                    let uu____2843 = tts e1 t  in
                    let uu____2845 =
                      let uu____2847 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2847
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2843 uu____2845 msg
                | FStar_Errors.Error (uu____2857,msg,uu____2859) ->
                    let uu____2862 = tts e1 t  in
                    let uu____2864 =
                      let uu____2866 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2866
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2862 uu____2864 msg))
  
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
             (fun uu____2919  ->
                let uu____2920 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2920)
             (fun uu____2926  ->
                let e1 =
                  let uu___486_2928 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___486_2928.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___486_2928.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___486_2928.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___486_2928.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___486_2928.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___486_2928.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___486_2928.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___486_2928.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___486_2928.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___486_2928.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___486_2928.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___486_2928.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___486_2928.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___486_2928.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___486_2928.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___486_2928.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___486_2928.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___486_2928.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___486_2928.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___486_2928.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___486_2928.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___486_2928.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___486_2928.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___486_2928.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___486_2928.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___486_2928.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___486_2928.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___486_2928.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___486_2928.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___486_2928.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___486_2928.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___486_2928.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___486_2928.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___486_2928.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___486_2928.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___486_2928.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___486_2928.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___486_2928.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___486_2928.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___486_2928.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___486_2928.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___486_2928.FStar_TypeChecker_Env.nbe)
                  }  in
                let e2 =
                  let uu___489_2931 = e1  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___489_2931.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___489_2931.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___489_2931.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___489_2931.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___489_2931.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___489_2931.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___489_2931.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___489_2931.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___489_2931.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___489_2931.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___489_2931.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___489_2931.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___489_2931.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___489_2931.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___489_2931.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___489_2931.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___489_2931.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___489_2931.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___489_2931.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___489_2931.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___489_2931.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___489_2931.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___489_2931.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___489_2931.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___489_2931.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___489_2931.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___489_2931.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___489_2931.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___489_2931.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___489_2931.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___489_2931.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___489_2931.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___489_2931.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___489_2931.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___489_2931.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___489_2931.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___489_2931.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___489_2931.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___489_2931.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___489_2931.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___489_2931.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___489_2931.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___493_2946  ->
                     match () with
                     | () ->
                         let uu____2955 =
                           FStar_TypeChecker_TcTerm.tc_term e2 t  in
                         (match uu____2955 with
                          | (t1,lc,g) ->
                              ret (t1, (lc.FStar_Syntax_Syntax.res_typ), g)))
                    ()
                with
                | FStar_Errors.Err (uu____2993,msg) ->
                    let uu____2997 = tts e2 t  in
                    let uu____2999 =
                      let uu____3001 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3001
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2997 uu____2999 msg
                | FStar_Errors.Error (uu____3011,msg,uu____3013) ->
                    let uu____3016 = tts e2 t  in
                    let uu____3018 =
                      let uu____3020 = FStar_TypeChecker_Env.all_binders e2
                         in
                      FStar_All.pipe_right uu____3020
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____3016 uu____3018 msg))
  
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
  fun uu____3054  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___518_3073 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___518_3073.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___518_3073.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___518_3073.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___518_3073.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___518_3073.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___518_3073.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___518_3073.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___518_3073.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___518_3073.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___518_3073.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___518_3073.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___518_3073.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____3098 = get_guard_policy ()  in
      bind uu____3098
        (fun old_pol  ->
           let uu____3104 = set_guard_policy pol  in
           bind uu____3104
             (fun uu____3108  ->
                bind t
                  (fun r  ->
                     let uu____3112 = set_guard_policy old_pol  in
                     bind uu____3112 (fun uu____3116  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____3120 = let uu____3125 = cur_goal ()  in trytac uu____3125  in
  bind uu____3120
    (fun uu___0_3132  ->
       match uu___0_3132 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____3138 = FStar_Options.peek ()  in ret uu____3138)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____3163  ->
             let uu____3164 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____3164)
          (fun uu____3169  ->
             let uu____3170 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____3170
               (fun uu____3174  ->
                  bind getopts
                    (fun opts  ->
                       let uu____3178 =
                         let uu____3179 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____3179.FStar_TypeChecker_Env.guard_f  in
                       match uu____3178 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____3183 = istrivial e f  in
                           if uu____3183
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____3196 =
                                          let uu____3202 =
                                            let uu____3204 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____3204
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____3202)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____3196);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____3210  ->
                                           let uu____3211 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____3211)
                                        (fun uu____3216  ->
                                           let uu____3217 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3217
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___547_3225 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___547_3225.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___547_3225.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___547_3225.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___547_3225.FStar_Tactics_Types.label)
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____3229  ->
                                           let uu____3230 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____3230)
                                        (fun uu____3235  ->
                                           let uu____3236 =
                                             mk_irrelevant_goal reason e f
                                               opts ""
                                              in
                                           bind uu____3236
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___554_3244 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___554_3244.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___554_3244.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___554_3244.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true;
                                                    FStar_Tactics_Types.label
                                                      =
                                                      (uu___554_3244.FStar_Tactics_Types.label)
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____3248  ->
                                           let uu____3249 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____3249)
                                        (fun uu____3253  ->
                                           try
                                             (fun uu___561_3258  ->
                                                match () with
                                                | () ->
                                                    let uu____3261 =
                                                      let uu____3263 =
                                                        let uu____3265 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____3265
                                                         in
                                                      Prims.op_Negation
                                                        uu____3263
                                                       in
                                                    if uu____3261
                                                    then
                                                      mlog
                                                        (fun uu____3272  ->
                                                           let uu____3273 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____3273)
                                                        (fun uu____3277  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___560_3282 ->
                                               mlog
                                                 (fun uu____3287  ->
                                                    let uu____3288 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____3288)
                                                 (fun uu____3292  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____3304 =
      let uu____3307 = cur_goal ()  in
      bind uu____3307
        (fun goal  ->
           let uu____3313 =
             let uu____3322 = FStar_Tactics_Types.goal_env goal  in
             __tc_lax uu____3322 t  in
           bind uu____3313
             (fun uu____3333  ->
                match uu____3333 with
                | (uu____3342,typ,uu____3344) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____3304
  
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
            let uu____3384 = mk_irrelevant_goal reason env phi opts label1
               in
            bind uu____3384 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____3396  ->
    let uu____3399 = cur_goal ()  in
    bind uu____3399
      (fun goal  ->
         let uu____3405 =
           let uu____3407 = FStar_Tactics_Types.goal_env goal  in
           let uu____3408 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____3407 uu____3408  in
         if uu____3405
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____3414 =
              let uu____3416 = FStar_Tactics_Types.goal_env goal  in
              let uu____3417 = FStar_Tactics_Types.goal_type goal  in
              tts uu____3416 uu____3417  in
            fail1 "Not a trivial goal: %s" uu____3414))
  
let divide : 'a 'b . FStar_BigInt.t -> 'a tac -> 'b tac -> ('a * 'b) tac =
  fun n1  ->
    fun l  ->
      fun r  ->
        bind get
          (fun p  ->
             let uu____3468 =
               try
                 (fun uu___617_3491  ->
                    match () with
                    | () ->
                        let uu____3502 =
                          let uu____3511 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____3511
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____3502) ()
               with | uu___616_3522 -> fail "divide: not enough goals"  in
             bind uu____3468
               (fun uu____3559  ->
                  match uu____3559 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___599_3585 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___599_3585.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___599_3585.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___599_3585.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___599_3585.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___599_3585.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___599_3585.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___599_3585.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___599_3585.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___599_3585.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___599_3585.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___599_3585.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____3586 = set lp  in
                      bind uu____3586
                        (fun uu____3594  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___605_3610 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___605_3610.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___605_3610.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___605_3610.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___605_3610.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___605_3610.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___605_3610.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___605_3610.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___605_3610.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___605_3610.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___605_3610.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___605_3610.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____3611 = set rp  in
                                     bind uu____3611
                                       (fun uu____3619  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___611_3635 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___611_3635.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___611_3635.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____3636 = set p'
                                                       in
                                                    bind uu____3636
                                                      (fun uu____3644  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____3650 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____3672 = divide FStar_BigInt.one f idtac  in
    bind uu____3672
      (fun uu____3685  -> match uu____3685 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____3723::uu____3724 ->
             let uu____3727 =
               let uu____3736 = map tau  in
               divide FStar_BigInt.one tau uu____3736  in
             bind uu____3727
               (fun uu____3754  ->
                  match uu____3754 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____3796 =
        bind t1
          (fun uu____3801  ->
             let uu____3802 = map t2  in
             bind uu____3802 (fun uu____3810  -> ret ()))
         in
      focus uu____3796
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3820  ->
    let uu____3823 =
      let uu____3826 = cur_goal ()  in
      bind uu____3826
        (fun goal  ->
           let uu____3835 =
             let uu____3842 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3842  in
           match uu____3835 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3851 =
                 let uu____3853 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3853  in
               if uu____3851
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3862 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3862 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3876 = new_uvar "intro" env' typ'  in
                  bind uu____3876
                    (fun uu____3893  ->
                       match uu____3893 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c))
                              in
                           let uu____3917 = set_solution goal sol  in
                           bind uu____3917
                             (fun uu____3923  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label
                                   in
                                let uu____3925 =
                                  let uu____3928 = bnorm_goal g  in
                                  replace_cur uu____3928  in
                                bind uu____3925 (fun uu____3930  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3935 =
                 let uu____3937 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3938 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3937 uu____3938  in
               fail1 "goal is not an arrow (%s)" uu____3935)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3823
  
let (intro_rec :
  unit -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder) tac) =
  fun uu____3956  ->
    let uu____3963 = cur_goal ()  in
    bind uu____3963
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3982 =
            let uu____3989 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3989  in
          match uu____3982 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____4002 =
                let uu____4004 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____4004  in
              if uu____4002
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____4021 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____4021
                    in
                 let bs =
                   let uu____4032 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____4032; b]  in
                 let env' =
                   let uu____4058 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____4058 bs  in
                 let uu____4059 =
                   let uu____4066 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____4066  in
                 bind uu____4059
                   (fun uu____4086  ->
                      match uu____4086 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____4100 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____4103 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____4100
                              FStar_Parser_Const.effect_Tot_lid uu____4103 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____4121 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____4121 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____4143 =
                                   let uu____4144 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____4144.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____4143
                                  in
                               let uu____4160 = set_solution goal tm  in
                               bind uu____4160
                                 (fun uu____4169  ->
                                    let uu____4170 =
                                      let uu____4173 =
                                        bnorm_goal
                                          (let uu___682_4176 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___682_4176.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___682_4176.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___682_4176.FStar_Tactics_Types.is_guard);
                                             FStar_Tactics_Types.label =
                                               (uu___682_4176.FStar_Tactics_Types.label)
                                           })
                                         in
                                      replace_cur uu____4173  in
                                    bind uu____4170
                                      (fun uu____4183  ->
                                         let uu____4184 =
                                           let uu____4189 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____4189, b)  in
                                         ret uu____4184)))))
          | FStar_Pervasives_Native.None  ->
              let uu____4198 =
                let uu____4200 = FStar_Tactics_Types.goal_env goal  in
                let uu____4201 = FStar_Tactics_Types.goal_type goal  in
                tts uu____4200 uu____4201  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____4198))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____4221 = cur_goal ()  in
    bind uu____4221
      (fun goal  ->
         mlog
           (fun uu____4228  ->
              let uu____4229 =
                let uu____4231 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____4231  in
              FStar_Util.print1 "norm: witness = %s\n" uu____4229)
           (fun uu____4237  ->
              let steps =
                let uu____4241 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____4241
                 in
              let t =
                let uu____4245 = FStar_Tactics_Types.goal_env goal  in
                let uu____4246 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____4245 uu____4246  in
              let uu____4247 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____4247))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____4272 =
          bind get
            (fun ps  ->
               let opts =
                 match ps.FStar_Tactics_Types.goals with
                 | g::uu____4280 -> g.FStar_Tactics_Types.opts
                 | uu____4283 -> FStar_Options.peek ()  in
               mlog
                 (fun uu____4288  ->
                    let uu____4289 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print1 "norm_term_env: t = %s\n" uu____4289)
                 (fun uu____4294  ->
                    let uu____4295 = __tc_lax e t  in
                    bind uu____4295
                      (fun uu____4316  ->
                         match uu____4316 with
                         | (t1,uu____4326,uu____4327) ->
                             let steps =
                               let uu____4331 =
                                 FStar_TypeChecker_Normalize.tr_norm_steps s
                                  in
                               FStar_List.append
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu____4331
                                in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1
                                in
                             mlog
                               (fun uu____4337  ->
                                  let uu____4338 =
                                    FStar_Syntax_Print.term_to_string t2  in
                                  FStar_Util.print1
                                    "norm_term_env: t' = %s\n" uu____4338)
                               (fun uu____4342  -> ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____4272
  
let (refine_intro : unit -> unit tac) =
  fun uu____4355  ->
    let uu____4358 =
      let uu____4361 = cur_goal ()  in
      bind uu____4361
        (fun g  ->
           let uu____4368 =
             let uu____4379 = FStar_Tactics_Types.goal_env g  in
             let uu____4380 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____4379 uu____4380
              in
           match uu____4368 with
           | (uu____4383,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____4409 =
                 let uu____4414 =
                   let uu____4419 =
                     let uu____4420 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____4420]  in
                   FStar_Syntax_Subst.open_term uu____4419 phi  in
                 match uu____4414 with
                 | (bvs,phi1) ->
                     let uu____4445 =
                       let uu____4446 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____4446  in
                     (uu____4445, phi1)
                  in
               (match uu____4409 with
                | (bv1,phi1) ->
                    let uu____4465 =
                      let uu____4468 = FStar_Tactics_Types.goal_env g  in
                      let uu____4469 =
                        let uu____4470 =
                          let uu____4473 =
                            let uu____4474 =
                              let uu____4481 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____4481)  in
                            FStar_Syntax_Syntax.NT uu____4474  in
                          [uu____4473]  in
                        FStar_Syntax_Subst.subst uu____4470 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____4468
                        uu____4469 g.FStar_Tactics_Types.opts
                        g.FStar_Tactics_Types.label
                       in
                    bind uu____4465
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____4490  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____4358
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____4513 = cur_goal ()  in
      bind uu____4513
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____4522 = FStar_Tactics_Types.goal_env goal  in
               let uu____4523 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____4522 uu____4523
             else FStar_Tactics_Types.goal_env goal  in
           let uu____4526 = __tc env t  in
           bind uu____4526
             (fun uu____4545  ->
                match uu____4545 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____4560  ->
                         let uu____4561 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____4563 =
                           let uu____4565 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____4565
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____4561 uu____4563)
                      (fun uu____4569  ->
                         let uu____4570 =
                           let uu____4573 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____4573 guard  in
                         bind uu____4570
                           (fun uu____4576  ->
                              mlog
                                (fun uu____4580  ->
                                   let uu____4581 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____4583 =
                                     let uu____4585 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____4585
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____4581 uu____4583)
                                (fun uu____4589  ->
                                   let uu____4590 =
                                     let uu____4594 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____4595 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____4594 typ uu____4595  in
                                   bind uu____4590
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____4605 =
                                             let uu____4607 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4607 t1  in
                                           let uu____4608 =
                                             let uu____4610 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____4610 typ  in
                                           let uu____4611 =
                                             let uu____4613 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4614 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____4613 uu____4614  in
                                           let uu____4615 =
                                             let uu____4617 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____4618 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____4617 uu____4618  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____4605 uu____4608 uu____4611
                                             uu____4615)))))))
  
let (t_exact :
  Prims.bool -> Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun try_refine  ->
    fun set_expected_typ1  ->
      fun tm  ->
        let uu____4644 =
          mlog
            (fun uu____4649  ->
               let uu____4650 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.print1 "t_exact: tm = %s\n" uu____4650)
            (fun uu____4655  ->
               let uu____4656 =
                 let uu____4663 = __exact_now set_expected_typ1 tm  in
                 catch uu____4663  in
               bind uu____4656
                 (fun uu___2_4672  ->
                    match uu___2_4672 with
                    | FStar_Util.Inr r -> ret ()
                    | FStar_Util.Inl e when Prims.op_Negation try_refine ->
                        traise e
                    | FStar_Util.Inl e ->
                        mlog
                          (fun uu____4683  ->
                             FStar_Util.print_string
                               "__exact_now failed, trying refine...\n")
                          (fun uu____4687  ->
                             let uu____4688 =
                               let uu____4695 =
                                 let uu____4698 =
                                   norm [FStar_Syntax_Embeddings.Delta]  in
                                 bind uu____4698
                                   (fun uu____4703  ->
                                      let uu____4704 = refine_intro ()  in
                                      bind uu____4704
                                        (fun uu____4708  ->
                                           __exact_now set_expected_typ1 tm))
                                  in
                               catch uu____4695  in
                             bind uu____4688
                               (fun uu___1_4715  ->
                                  match uu___1_4715 with
                                  | FStar_Util.Inr r ->
                                      mlog
                                        (fun uu____4724  ->
                                           FStar_Util.print_string
                                             "__exact_now: failed after refining too\n")
                                        (fun uu____4727  -> ret ())
                                  | FStar_Util.Inl uu____4728 ->
                                      mlog
                                        (fun uu____4730  ->
                                           FStar_Util.print_string
                                             "__exact_now: was not a refinement\n")
                                        (fun uu____4733  -> traise e)))))
           in
        FStar_All.pipe_left (wrap_err "exact") uu____4644
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____4785 = f x  in
          bind uu____4785
            (fun y  ->
               let uu____4793 = mapM f xs  in
               bind uu____4793 (fun ys  -> ret (y :: ys)))
  
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
          let uu____4865 = do_unify e ty1 ty2  in
          bind uu____4865
            (fun uu___3_4879  ->
               if uu___3_4879
               then ret acc
               else
                 (let uu____4899 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____4899 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____4920 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____4922 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____4920
                        uu____4922
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4939 =
                        let uu____4941 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4941  in
                      if uu____4939
                      then fail "Codomain is effectful"
                      else
                        (let uu____4965 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4965
                           (fun uu____4992  ->
                              match uu____4992 with
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
      let uu____5082 =
        mlog
          (fun uu____5087  ->
             let uu____5088 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_apply: tm = %s\n" uu____5088)
          (fun uu____5093  ->
             let uu____5094 = cur_goal ()  in
             bind uu____5094
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____5102 = __tc e tm  in
                  bind uu____5102
                    (fun uu____5123  ->
                       match uu____5123 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____5136 =
                             let uu____5147 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____5147  in
                           bind uu____5136
                             (fun uvs  ->
                                let fix_qual q =
                                  match q with
                                  | FStar_Pervasives_Native.Some
                                      (FStar_Syntax_Syntax.Meta uu____5185)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Syntax.Implicit false)
                                  | uu____5189 -> q  in
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____5212  ->
                                       fun w  ->
                                         match uu____5212 with
                                         | (uvt,q,uu____5230) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, (fix_qual q))]) uvs tm1
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
                                                              (let uu___843_5358
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___843_5358.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___843_5358.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false;
                                                                 FStar_Tactics_Types.label
                                                                   =
                                                                   (uu___843_5358.FStar_Tactics_Types.label)
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
      FStar_All.pipe_left (wrap_err "apply") uu____5082
  
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
                                                                    (let uu___953_6740
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___953_6740.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___953_6740.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___953_6740.FStar_Tactics_Types.is_guard);
                                                                    FStar_Tactics_Types.label
                                                                    =
                                                                    (uu___953_6740.FStar_Tactics_Types.label)
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
                                                                    let uu___958_6761
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___958_6761.FStar_TypeChecker_Env.nbe)
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
    | uu____6994 ->
        let uu____6997 = FStar_Syntax_Util.unb2t typ  in
        (match uu____6997 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             ((let uu____7012 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "GG t = %s\n" uu____7012);
              (let uu____7015 = FStar_Syntax_Util.head_and_args t  in
               match uu____7015 with
               | (hd1,args) ->
                   let uu____7064 =
                     let uu____7079 =
                       let uu____7080 = FStar_Syntax_Subst.compress hd1  in
                       uu____7080.FStar_Syntax_Syntax.n  in
                     (uu____7079, args)  in
                   (match uu____7064 with
                    | (FStar_Syntax_Syntax.Tm_fvar
                       fv,(uu____7100,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit uu____7101))::
                       (e1,FStar_Pervasives_Native.None )::(e2,FStar_Pervasives_Native.None
                                                            )::[])
                        when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.op_Eq
                        ->
                        ((let uu____7166 =
                            FStar_Syntax_Print.term_to_string e1  in
                          let uu____7168 =
                            FStar_Syntax_Print.term_to_string e2  in
                          FStar_Util.print2 "wat %s -- %s\n" uu____7166
                            uu____7168);
                         FStar_Pervasives_Native.Some (e1, e2))
                    | uu____7175 -> FStar_Pervasives_Native.None))))
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____7212 = destruct_eq' typ  in
    match uu____7212 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____7242 = FStar_Syntax_Util.un_squash typ  in
        (match uu____7242 with
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
        let uu____7311 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____7311 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu____7369 = aux e'  in
               FStar_Util.map_opt uu____7369
                 (fun uu____7400  ->
                    match uu____7400 with
                    | (e'',bv,bvs) -> (e'', bv, (bv' :: bvs))))
         in
      let uu____7426 = aux e  in
      FStar_Util.map_opt uu____7426
        (fun uu____7457  ->
           match uu____7457 with
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
          let uu____7531 =
            let uu____7542 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____7542  in
          FStar_Util.map_opt uu____7531
            (fun uu____7560  ->
               match uu____7560 with
               | (e0,b11,bvs) ->
                   let s1 bv =
                     let uu___1055_7582 = bv  in
                     let uu____7583 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___1055_7582.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___1055_7582.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____7583
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___1059_7591 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____7592 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____7601 =
                       let uu____7604 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____7604  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___1059_7591.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____7592;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____7601;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___1059_7591.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___1059_7591.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___1059_7591.FStar_Syntax_Syntax.ctx_uvar_range);
                       FStar_Syntax_Syntax.ctx_uvar_meta =
                         (uu___1059_7591.FStar_Syntax_Syntax.ctx_uvar_meta)
                     }  in
                   let uu___1062_7605 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1062_7605.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___1062_7605.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___1062_7605.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1062_7605.FStar_Tactics_Types.label)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____7616 =
      let uu____7619 = cur_goal ()  in
      bind uu____7619
        (fun goal  ->
           let uu____7627 = h  in
           match uu____7627 with
           | (bv,uu____7631) ->
               mlog
                 (fun uu____7639  ->
                    let uu____7640 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____7642 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____7640
                      uu____7642)
                 (fun uu____7647  ->
                    let uu____7648 =
                      let uu____7659 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____7659  in
                    match uu____7648 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                        let uu____7686 =
                          destruct_eq bv1.FStar_Syntax_Syntax.sort  in
                        (match uu____7686 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____7701 =
                               let uu____7702 = FStar_Syntax_Subst.compress x
                                  in
                               uu____7702.FStar_Syntax_Syntax.n  in
                             (match uu____7701 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv2 =
                                    let uu___1085_7719 = bv2  in
                                    let uu____7720 =
                                      FStar_Syntax_Subst.subst s
                                        bv2.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1085_7719.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1085_7719.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____7720
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv1 :: bvs1)  in
                                  let new_goal =
                                    let uu___1089_7728 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____7729 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____7738 =
                                      let uu____7741 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____7741
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___1089_7728.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____7729;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____7738;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___1089_7728.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___1089_7728.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___1089_7728.FStar_Syntax_Syntax.ctx_uvar_range);
                                      FStar_Syntax_Syntax.ctx_uvar_meta =
                                        (uu___1089_7728.FStar_Syntax_Syntax.ctx_uvar_meta)
                                    }  in
                                  replace_cur
                                    (let uu___1092_7744 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___1092_7744.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___1092_7744.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___1092_7744.FStar_Tactics_Types.is_guard);
                                       FStar_Tactics_Types.label =
                                         (uu___1092_7744.FStar_Tactics_Types.label)
                                     })
                              | uu____7745 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____7747 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____7616
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____7777 =
        let uu____7780 = cur_goal ()  in
        bind uu____7780
          (fun goal  ->
             let uu____7791 = b  in
             match uu____7791 with
             | (bv,uu____7795) ->
                 let bv' =
                   let uu____7801 =
                     let uu___1103_7802 = bv  in
                     let uu____7803 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____7803;
                       FStar_Syntax_Syntax.index =
                         (uu___1103_7802.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___1103_7802.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____7801  in
                 let s1 =
                   let uu____7808 =
                     let uu____7809 =
                       let uu____7816 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____7816)  in
                     FStar_Syntax_Syntax.NT uu____7809  in
                   [uu____7808]  in
                 let uu____7821 = subst_goal bv bv' s1 goal  in
                 (match uu____7821 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____7777
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____7843 =
      let uu____7846 = cur_goal ()  in
      bind uu____7846
        (fun goal  ->
           let uu____7855 = b  in
           match uu____7855 with
           | (bv,uu____7859) ->
               let uu____7864 =
                 let uu____7875 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____7875  in
               (match uu____7864 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                    let uu____7902 = FStar_Syntax_Util.type_u ()  in
                    (match uu____7902 with
                     | (ty,u) ->
                         let uu____7911 = new_uvar "binder_retype" e0 ty  in
                         bind uu____7911
                           (fun uu____7930  ->
                              match uu____7930 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___1127_7940 = bv1  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___1127_7940.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___1127_7940.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____7944 =
                                      let uu____7945 =
                                        let uu____7952 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv1, uu____7952)  in
                                      FStar_Syntax_Syntax.NT uu____7945  in
                                    [uu____7944]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___1132_7964 = b1  in
                                         let uu____7965 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___1132_7964.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___1132_7964.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____7965
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____7972  ->
                                       let new_goal =
                                         let uu____7974 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____7975 =
                                           let uu____7976 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____7976
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____7974 uu____7975
                                          in
                                       let uu____7977 = add_goals [new_goal]
                                          in
                                       bind uu____7977
                                         (fun uu____7982  ->
                                            let uu____7983 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv1.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____7983
                                              goal.FStar_Tactics_Types.opts
                                              goal.FStar_Tactics_Types.label))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____7843
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____8009 =
        let uu____8012 = cur_goal ()  in
        bind uu____8012
          (fun goal  ->
             let uu____8021 = b  in
             match uu____8021 with
             | (bv,uu____8025) ->
                 let uu____8030 =
                   let uu____8041 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____8041  in
                 (match uu____8030 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bv1,bvs) ->
                      let steps =
                        let uu____8071 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____8071
                         in
                      let sort' =
                        normalize steps e0 bv1.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___1153_8076 = bv1  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___1153_8076.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___1153_8076.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____8078 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____8078))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____8009
  
let (revert : unit -> unit tac) =
  fun uu____8091  ->
    let uu____8094 = cur_goal ()  in
    bind uu____8094
      (fun goal  ->
         let uu____8100 =
           let uu____8107 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8107  in
         match uu____8100 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____8124 =
                 let uu____8127 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____8127  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____8124
                in
             let uu____8142 = new_uvar "revert" env' typ'  in
             bind uu____8142
               (fun uu____8158  ->
                  match uu____8158 with
                  | (r,u_r) ->
                      let uu____8167 =
                        let uu____8170 =
                          let uu____8171 =
                            let uu____8172 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____8172.FStar_Syntax_Syntax.pos  in
                          let uu____8175 =
                            let uu____8180 =
                              let uu____8181 =
                                let uu____8190 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____8190  in
                              [uu____8181]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____8180  in
                          uu____8175 FStar_Pervasives_Native.None uu____8171
                           in
                        set_solution goal uu____8170  in
                      bind uu____8167
                        (fun uu____8209  ->
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
      let uu____8223 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____8223
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____8239 = cur_goal ()  in
    bind uu____8239
      (fun goal  ->
         mlog
           (fun uu____8247  ->
              let uu____8248 = FStar_Syntax_Print.binder_to_string b  in
              let uu____8250 =
                let uu____8252 =
                  let uu____8254 =
                    let uu____8263 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____8263  in
                  FStar_All.pipe_right uu____8254 FStar_List.length  in
                FStar_All.pipe_right uu____8252 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____8248 uu____8250)
           (fun uu____8284  ->
              let uu____8285 =
                let uu____8296 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____8296  in
              match uu____8285 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bv1,bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____8341 =
                          free_in bv1 bv'.FStar_Syntax_Syntax.sort  in
                        if uu____8341
                        then
                          let uu____8346 =
                            let uu____8348 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____8348
                             in
                          fail uu____8346
                        else check1 bvs2
                     in
                  let uu____8353 =
                    let uu____8355 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv1 uu____8355  in
                  if uu____8353
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____8362 = check1 bvs  in
                     bind uu____8362
                       (fun uu____8368  ->
                          let env' = push_bvs e' bvs  in
                          let uu____8370 =
                            let uu____8377 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____8377  in
                          bind uu____8370
                            (fun uu____8387  ->
                               match uu____8387 with
                               | (ut,uvar_ut) ->
                                   let uu____8396 = set_solution goal ut  in
                                   bind uu____8396
                                     (fun uu____8401  ->
                                        let uu____8402 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label
                                           in
                                        replace_cur uu____8402))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____8410  ->
    let uu____8413 = cur_goal ()  in
    bind uu____8413
      (fun goal  ->
         let uu____8419 =
           let uu____8426 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____8426  in
         match uu____8419 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____8435) ->
             let uu____8440 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____8440)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____8453 = cur_goal ()  in
    bind uu____8453
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8463 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____8463  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8466  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____8479 = cur_goal ()  in
    bind uu____8479
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____8489 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____8489  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____8492  -> add_goals [g']))
  
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
            let uu____8533 = FStar_Syntax_Subst.compress t  in
            uu____8533.FStar_Syntax_Syntax.n  in
          let uu____8536 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___1337_8543 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___1337_8543.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___1337_8543.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____8536
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____8560 =
                   let uu____8561 = FStar_Syntax_Subst.compress t1  in
                   uu____8561.FStar_Syntax_Syntax.n  in
                 match uu____8560 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____8592 = ff hd1  in
                     bind uu____8592
                       (fun hd2  ->
                          let fa uu____8618 =
                            match uu____8618 with
                            | (a,q) ->
                                let uu____8639 = ff a  in
                                bind uu____8639 (fun a1  -> ret (a1, q))
                             in
                          let uu____8658 = mapM fa args  in
                          bind uu____8658
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____8740 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____8740 with
                      | (bs1,t') ->
                          let uu____8749 =
                            let uu____8752 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____8752 t'  in
                          bind uu____8749
                            (fun t''  ->
                               let uu____8756 =
                                 let uu____8757 =
                                   let uu____8776 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____8785 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____8776, uu____8785, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____8757  in
                               ret uu____8756))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____8860 = ff hd1  in
                     bind uu____8860
                       (fun hd2  ->
                          let ffb br =
                            let uu____8875 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____8875 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____8907 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____8907  in
                                let uu____8908 = ff1 e  in
                                bind uu____8908
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____8923 = mapM ffb brs  in
                          bind uu____8923
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____8967;
                          FStar_Syntax_Syntax.lbtyp = uu____8968;
                          FStar_Syntax_Syntax.lbeff = uu____8969;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____8971;
                          FStar_Syntax_Syntax.lbpos = uu____8972;_}::[]),e)
                     ->
                     let lb =
                       let uu____9000 =
                         let uu____9001 = FStar_Syntax_Subst.compress t1  in
                         uu____9001.FStar_Syntax_Syntax.n  in
                       match uu____9000 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____9005) -> lb
                       | uu____9021 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____9031 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9031
                         (fun def1  ->
                            ret
                              (let uu___1290_9037 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1290_9037.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1290_9037.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1290_9037.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1290_9037.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1290_9037.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1290_9037.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9038 = fflb lb  in
                     bind uu____9038
                       (fun lb1  ->
                          let uu____9048 =
                            let uu____9053 =
                              let uu____9054 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____9054]  in
                            FStar_Syntax_Subst.open_term uu____9053 e  in
                          match uu____9048 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____9084 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____9084  in
                              let uu____9085 = ff1 e1  in
                              bind uu____9085
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____9132 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____9132
                         (fun def  ->
                            ret
                              (let uu___1308_9138 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___1308_9138.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1308_9138.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___1308_9138.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1308_9138.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1308_9138.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1308_9138.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____9139 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____9139 with
                      | (lbs1,e1) ->
                          let uu____9154 = mapM fflb lbs1  in
                          bind uu____9154
                            (fun lbs2  ->
                               let uu____9166 = ff e1  in
                               bind uu____9166
                                 (fun e2  ->
                                    let uu____9174 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____9174 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____9245 = ff t2  in
                     bind uu____9245
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____9276 = ff t2  in
                     bind uu____9276
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____9283 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___1332_9290 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___1332_9290.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___1332_9290.FStar_Syntax_Syntax.vars)
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
              let uu____9337 =
                FStar_TypeChecker_TcTerm.tc_term
                  (let uu___1345_9346 = env  in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___1345_9346.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___1345_9346.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___1345_9346.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___1345_9346.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___1345_9346.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___1345_9346.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___1345_9346.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___1345_9346.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___1345_9346.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___1345_9346.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.is_pattern =
                       (uu___1345_9346.FStar_TypeChecker_Env.is_pattern);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___1345_9346.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___1345_9346.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___1345_9346.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___1345_9346.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___1345_9346.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___1345_9346.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___1345_9346.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___1345_9346.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___1345_9346.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___1345_9346.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___1345_9346.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___1345_9346.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___1345_9346.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___1345_9346.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___1345_9346.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___1345_9346.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___1345_9346.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___1345_9346.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___1345_9346.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___1345_9346.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___1345_9346.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___1345_9346.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___1345_9346.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___1345_9346.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___1345_9346.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___1345_9346.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.is_native_tactic =
                       (uu___1345_9346.FStar_TypeChecker_Env.is_native_tactic);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___1345_9346.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___1345_9346.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___1345_9346.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___1345_9346.FStar_TypeChecker_Env.nbe)
                   }) t
                 in
              match uu____9337 with
              | (t1,lcomp,g) ->
                  let uu____9353 =
                    (let uu____9357 =
                       FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                     Prims.op_Negation uu____9357) ||
                      (let uu____9360 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____9360)
                     in
                  if uu____9353
                  then ret t1
                  else
                    (let rewrite_eq =
                       let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                       let uu____9371 = new_uvar "pointwise_rec" env typ  in
                       bind uu____9371
                         (fun uu____9388  ->
                            match uu____9388 with
                            | (ut,uvar_ut) ->
                                (log ps
                                   (fun uu____9401  ->
                                      let uu____9402 =
                                        FStar_Syntax_Print.term_to_string t1
                                         in
                                      let uu____9404 =
                                        FStar_Syntax_Print.term_to_string ut
                                         in
                                      FStar_Util.print2
                                        "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                        uu____9402 uu____9404);
                                 (let uu____9407 =
                                    let uu____9410 =
                                      let uu____9411 =
                                        FStar_TypeChecker_TcTerm.universe_of
                                          env typ
                                         in
                                      FStar_Syntax_Util.mk_eq2 uu____9411 typ
                                        t1 ut
                                       in
                                    add_irrelevant_goal
                                      "pointwise_rec equation" env uu____9410
                                      opts label1
                                     in
                                  bind uu____9407
                                    (fun uu____9415  ->
                                       let uu____9416 =
                                         bind tau
                                           (fun uu____9422  ->
                                              let ut1 =
                                                FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                  env ut
                                                 in
                                              log ps
                                                (fun uu____9428  ->
                                                   let uu____9429 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   let uu____9431 =
                                                     FStar_Syntax_Print.term_to_string
                                                       ut1
                                                      in
                                                   FStar_Util.print2
                                                     "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                     uu____9429 uu____9431);
                                              ret ut1)
                                          in
                                       focus uu____9416))))
                        in
                     let uu____9434 = catch rewrite_eq  in
                     bind uu____9434
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
          let uu____9646 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____9646
            (fun t1  ->
               let uu____9654 =
                 f env
                   (let uu___1422_9662 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___1422_9662.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___1422_9662.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____9654
                 (fun uu____9678  ->
                    match uu____9678 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____9701 =
                               let uu____9702 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____9702.FStar_Syntax_Syntax.n  in
                             match uu____9701 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____9739 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____9739
                                   (fun uu____9761  ->
                                      match uu____9761 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____9777 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____9777
                                            (fun uu____9801  ->
                                               match uu____9801 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___1402_9831 =
                                                         t3  in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___1402_9831.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___1402_9831.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____9873 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____9873 with
                                  | (bs1,t') ->
                                      let uu____9888 =
                                        let uu____9895 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____9895 ctrl1 t'
                                         in
                                      bind uu____9888
                                        (fun uu____9910  ->
                                           match uu____9910 with
                                           | (t'',ctrl2) ->
                                               let uu____9925 =
                                                 let uu____9932 =
                                                   let uu___1415_9935 = t4
                                                      in
                                                   let uu____9938 =
                                                     let uu____9939 =
                                                       let uu____9958 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____9967 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____9958,
                                                         uu____9967, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____9939
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____9938;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___1415_9935.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___1415_9935.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____9932, ctrl2)  in
                                               ret uu____9925))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____10020 -> ret (t3, ctrl1))))

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
              let uu____10066 = ctrl_tac_fold f env ctrl t  in
              bind uu____10066
                (fun uu____10087  ->
                   match uu____10087 with
                   | (t1,ctrl1) ->
                       let uu____10102 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____10102
                         (fun uu____10126  ->
                            match uu____10126 with
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
                let uu____10217 =
                  let uu____10225 =
                    add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                      opts label1
                     in
                  bind uu____10225
                    (fun uu____10236  ->
                       let uu____10237 = ctrl t1  in
                       bind uu____10237
                         (fun res  ->
                            let uu____10263 = trivial ()  in
                            bind uu____10263 (fun uu____10272  -> ret res)))
                   in
                bind uu____10217
                  (fun uu____10290  ->
                     match uu____10290 with
                     | (should_rewrite,ctrl1) ->
                         if Prims.op_Negation should_rewrite
                         then ret (t1, ctrl1)
                         else
                           (let uu____10319 =
                              FStar_TypeChecker_TcTerm.tc_term
                                (let uu___1452_10328 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___1452_10328.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___1452_10328.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___1452_10328.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___1452_10328.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___1452_10328.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___1452_10328.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___1452_10328.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___1452_10328.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___1452_10328.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___1452_10328.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___1452_10328.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___1452_10328.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___1452_10328.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___1452_10328.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___1452_10328.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___1452_10328.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___1452_10328.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___1452_10328.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___1452_10328.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___1452_10328.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___1452_10328.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___1452_10328.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___1452_10328.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___1452_10328.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___1452_10328.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___1452_10328.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___1452_10328.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___1452_10328.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___1452_10328.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___1452_10328.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___1452_10328.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___1452_10328.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___1452_10328.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___1452_10328.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___1452_10328.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___1452_10328.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___1452_10328.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___1452_10328.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___1452_10328.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___1452_10328.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___1452_10328.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___1452_10328.FStar_TypeChecker_Env.nbe)
                                 }) t1
                               in
                            match uu____10319 with
                            | (t2,lcomp,g) ->
                                let uu____10339 =
                                  (let uu____10343 =
                                     FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                       lcomp
                                      in
                                   Prims.op_Negation uu____10343) ||
                                    (let uu____10346 =
                                       FStar_TypeChecker_Env.is_trivial g  in
                                     Prims.op_Negation uu____10346)
                                   in
                                if uu____10339
                                then ret (t2, globalStop)
                                else
                                  (let typ =
                                     lcomp.FStar_Syntax_Syntax.res_typ  in
                                   let uu____10362 =
                                     new_uvar "pointwise_rec" env typ  in
                                   bind uu____10362
                                     (fun uu____10383  ->
                                        match uu____10383 with
                                        | (ut,uvar_ut) ->
                                            (log ps
                                               (fun uu____10400  ->
                                                  let uu____10401 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t2
                                                     in
                                                  let uu____10403 =
                                                    FStar_Syntax_Print.term_to_string
                                                      ut
                                                     in
                                                  FStar_Util.print2
                                                    "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                    uu____10401 uu____10403);
                                             (let uu____10406 =
                                                let uu____10409 =
                                                  let uu____10410 =
                                                    FStar_TypeChecker_TcTerm.universe_of
                                                      env typ
                                                     in
                                                  FStar_Syntax_Util.mk_eq2
                                                    uu____10410 typ t2 ut
                                                   in
                                                add_irrelevant_goal
                                                  "rewrite_rec equation" env
                                                  uu____10409 opts label1
                                                 in
                                              bind uu____10406
                                                (fun uu____10418  ->
                                                   let uu____10419 =
                                                     bind rewriter
                                                       (fun uu____10433  ->
                                                          let ut1 =
                                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                              env ut
                                                             in
                                                          log ps
                                                            (fun uu____10439 
                                                               ->
                                                               let uu____10440
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t2
                                                                  in
                                                               let uu____10442
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   ut1
                                                                  in
                                                               FStar_Util.print2
                                                                 "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                                 uu____10440
                                                                 uu____10442);
                                                          ret (ut1, ctrl1))
                                                      in
                                                   focus uu____10419)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term -> (Prims.bool * FStar_BigInt.t) tac) ->
    unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____10487 =
        bind get
          (fun ps  ->
             let uu____10497 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10497 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10535  ->
                       let uu____10536 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____10536);
                  bind dismiss_all
                    (fun uu____10541  ->
                       let uu____10542 =
                         let uu____10549 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10549
                           keepGoing gt1
                          in
                       bind uu____10542
                         (fun uu____10559  ->
                            match uu____10559 with
                            | (gt',uu____10567) ->
                                (log ps
                                   (fun uu____10571  ->
                                      let uu____10572 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____10572);
                                 (let uu____10575 = push_goals gs  in
                                  bind uu____10575
                                    (fun uu____10580  ->
                                       let uu____10581 =
                                         let uu____10584 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____10584]  in
                                       add_goals uu____10581)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____10487
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____10609 =
        bind get
          (fun ps  ->
             let uu____10619 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____10619 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____10657  ->
                       let uu____10658 =
                         FStar_Syntax_Print.term_to_string gt1  in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____10658);
                  bind dismiss_all
                    (fun uu____10663  ->
                       let uu____10664 =
                         let uu____10667 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts
                              g.FStar_Tactics_Types.label) uu____10667 gt1
                          in
                       bind uu____10664
                         (fun gt'  ->
                            log ps
                              (fun uu____10675  ->
                                 let uu____10676 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____10676);
                            (let uu____10679 = push_goals gs  in
                             bind uu____10679
                               (fun uu____10684  ->
                                  let uu____10685 =
                                    let uu____10688 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____10688]  in
                                  add_goals uu____10685))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____10609
  
let (trefl : unit -> unit tac) =
  fun uu____10701  ->
    let uu____10704 =
      let uu____10707 = cur_goal ()  in
      bind uu____10707
        (fun g  ->
           let uu____10725 =
             let uu____10730 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____10730  in
           match uu____10725 with
           | FStar_Pervasives_Native.Some t ->
               let uu____10738 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____10738 with
                | (hd1,args) ->
                    let uu____10777 =
                      let uu____10790 =
                        let uu____10791 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____10791.FStar_Syntax_Syntax.n  in
                      (uu____10790, args)  in
                    (match uu____10777 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____10805::(l,uu____10807)::(r,uu____10809)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____10856 =
                           let uu____10860 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____10860 l r  in
                         bind uu____10856
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____10871 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10871 l
                                    in
                                 let r1 =
                                   let uu____10873 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____10873 r
                                    in
                                 let uu____10874 =
                                   let uu____10878 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____10878 l1 r1  in
                                 bind uu____10874
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____10888 =
                                           let uu____10890 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10890 l1  in
                                         let uu____10891 =
                                           let uu____10893 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____10893 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____10888 uu____10891))))
                     | (hd2,uu____10896) ->
                         let uu____10913 =
                           let uu____10915 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____10915 t  in
                         fail1 "trefl: not an equality (%s)" uu____10913))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____10704
  
let (dup : unit -> unit tac) =
  fun uu____10932  ->
    let uu____10935 = cur_goal ()  in
    bind uu____10935
      (fun g  ->
         let uu____10941 =
           let uu____10948 = FStar_Tactics_Types.goal_env g  in
           let uu____10949 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____10948 uu____10949  in
         bind uu____10941
           (fun uu____10959  ->
              match uu____10959 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___1544_10969 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___1544_10969.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___1544_10969.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___1544_10969.FStar_Tactics_Types.is_guard);
                      FStar_Tactics_Types.label =
                        (uu___1544_10969.FStar_Tactics_Types.label)
                    }  in
                  bind __dismiss
                    (fun uu____10972  ->
                       let uu____10973 =
                         let uu____10976 = FStar_Tactics_Types.goal_env g  in
                         let uu____10977 =
                           let uu____10978 =
                             let uu____10979 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____10980 =
                               FStar_Tactics_Types.goal_type g  in
                             FStar_TypeChecker_TcTerm.universe_of uu____10979
                               uu____10980
                              in
                           let uu____10981 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____10982 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____10978 uu____10981 u
                             uu____10982
                            in
                         add_irrelevant_goal "dup equation" uu____10976
                           uu____10977 g.FStar_Tactics_Types.opts
                           g.FStar_Tactics_Types.label
                          in
                       bind uu____10973
                         (fun uu____10986  ->
                            let uu____10987 = add_goals [g']  in
                            bind uu____10987 (fun uu____10991  -> ret ())))))
  
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
              let uu____11117 = f x y  in
              if uu____11117 then aux (x :: acc) xs ys else (acc, xs, ys)
          | uu____11140 -> (acc, l11, l21)  in
        let uu____11155 = aux [] l1 l2  in
        match uu____11155 with | (pr,t1,t2) -> ((FStar_List.rev pr), t1, t2)
  
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
      let uu____11261 = get_phi g1  in
      match uu____11261 with
      | FStar_Pervasives_Native.None  -> fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu____11268 = get_phi g2  in
          (match uu____11268 with
           | FStar_Pervasives_Native.None  -> fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               let uu____11281 =
                 longest_prefix FStar_Syntax_Syntax.eq_binding
                   (FStar_List.rev gamma1) (FStar_List.rev gamma2)
                  in
               (match uu____11281 with
                | (gamma,r1,r2) ->
                    let t1 =
                      let uu____11312 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r1)
                         in
                      close_forall_no_univs1 uu____11312 phi1  in
                    let t2 =
                      let uu____11322 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_List.rev r2)
                         in
                      close_forall_no_univs1 uu____11322 phi2  in
                    let uu____11331 =
                      set_solution g1 FStar_Syntax_Util.exp_unit  in
                    bind uu____11331
                      (fun uu____11336  ->
                         let uu____11337 =
                           set_solution g2 FStar_Syntax_Util.exp_unit  in
                         bind uu____11337
                           (fun uu____11344  ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2  in
                              let nenv =
                                let uu___1595_11349 =
                                  FStar_Tactics_Types.goal_env g1  in
                                let uu____11350 =
                                  FStar_Util.smap_create
                                    (Prims.parse_int "100")
                                   in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___1595_11349.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___1595_11349.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___1595_11349.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___1595_11349.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    uu____11350;
                                  FStar_TypeChecker_Env.modules =
                                    (uu___1595_11349.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___1595_11349.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___1595_11349.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___1595_11349.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___1595_11349.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___1595_11349.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___1595_11349.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___1595_11349.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___1595_11349.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___1595_11349.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___1595_11349.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___1595_11349.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___1595_11349.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___1595_11349.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___1595_11349.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___1595_11349.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___1595_11349.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___1595_11349.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___1595_11349.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___1595_11349.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___1595_11349.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___1595_11349.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___1595_11349.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.check_type_of =
                                    (uu___1595_11349.FStar_TypeChecker_Env.check_type_of);
                                  FStar_TypeChecker_Env.use_bv_sorts =
                                    (uu___1595_11349.FStar_TypeChecker_Env.use_bv_sorts);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___1595_11349.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___1595_11349.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___1595_11349.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___1595_11349.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___1595_11349.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___1595_11349.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___1595_11349.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.is_native_tactic =
                                    (uu___1595_11349.FStar_TypeChecker_Env.is_native_tactic);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___1595_11349.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___1595_11349.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___1595_11349.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___1595_11349.FStar_TypeChecker_Env.nbe)
                                }  in
                              let uu____11354 =
                                mk_irrelevant_goal "joined" nenv ng
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label
                                 in
                              bind uu____11354
                                (fun goal  ->
                                   mlog
                                     (fun uu____11364  ->
                                        let uu____11365 =
                                          goal_to_string_verbose g1  in
                                        let uu____11367 =
                                          goal_to_string_verbose g2  in
                                        let uu____11369 =
                                          goal_to_string_verbose goal  in
                                        FStar_Util.print3
                                          "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                          uu____11365 uu____11367 uu____11369)
                                     (fun uu____11373  -> ret goal))))))
  
let (join : unit -> unit tac) =
  fun uu____11381  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu____11397 =
               set
                 (let uu___1610_11402 = ps  in
                  {
                    FStar_Tactics_Types.main_context =
                      (uu___1610_11402.FStar_Tactics_Types.main_context);
                    FStar_Tactics_Types.main_goal =
                      (uu___1610_11402.FStar_Tactics_Types.main_goal);
                    FStar_Tactics_Types.all_implicits =
                      (uu___1610_11402.FStar_Tactics_Types.all_implicits);
                    FStar_Tactics_Types.goals = gs;
                    FStar_Tactics_Types.smt_goals =
                      (uu___1610_11402.FStar_Tactics_Types.smt_goals);
                    FStar_Tactics_Types.depth =
                      (uu___1610_11402.FStar_Tactics_Types.depth);
                    FStar_Tactics_Types.__dump =
                      (uu___1610_11402.FStar_Tactics_Types.__dump);
                    FStar_Tactics_Types.psc =
                      (uu___1610_11402.FStar_Tactics_Types.psc);
                    FStar_Tactics_Types.entry_range =
                      (uu___1610_11402.FStar_Tactics_Types.entry_range);
                    FStar_Tactics_Types.guard_policy =
                      (uu___1610_11402.FStar_Tactics_Types.guard_policy);
                    FStar_Tactics_Types.freshness =
                      (uu___1610_11402.FStar_Tactics_Types.freshness);
                    FStar_Tactics_Types.tac_verb_dbg =
                      (uu___1610_11402.FStar_Tactics_Types.tac_verb_dbg);
                    FStar_Tactics_Types.local_state =
                      (uu___1610_11402.FStar_Tactics_Types.local_state)
                  })
                in
             bind uu____11397
               (fun uu____11405  ->
                  let uu____11406 = join_goals g1 g2  in
                  bind uu____11406 (fun g12  -> add_goals [g12]))
         | uu____11411 -> fail "join: less than 2 goals")
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____11427 =
      let uu____11430 = cur_goal ()  in
      bind uu____11430
        (fun g  ->
           FStar_Options.push ();
           (let uu____11443 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____11443);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___1621_11450 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___1621_11450.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___1621_11450.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___1621_11450.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (uu___1621_11450.FStar_Tactics_Types.label)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____11427
  
let (top_env : unit -> env tac) =
  fun uu____11467  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____11482  ->
    let uu____11486 = cur_goal ()  in
    bind uu____11486
      (fun g  ->
         let uu____11493 =
           (FStar_Options.lax ()) ||
             (let uu____11496 = FStar_Tactics_Types.goal_env g  in
              uu____11496.FStar_TypeChecker_Env.lax)
            in
         ret uu____11493)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____11513 =
        mlog
          (fun uu____11518  ->
             let uu____11519 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____11519)
          (fun uu____11524  ->
             let uu____11525 = cur_goal ()  in
             bind uu____11525
               (fun goal  ->
                  let env =
                    let uu____11533 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____11533 ty  in
                  let uu____11534 = __tc_ghost env tm  in
                  bind uu____11534
                    (fun uu____11553  ->
                       match uu____11553 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____11567  ->
                                let uu____11568 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____11568)
                             (fun uu____11572  ->
                                mlog
                                  (fun uu____11575  ->
                                     let uu____11576 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____11576)
                                  (fun uu____11581  ->
                                     let uu____11582 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____11582
                                       (fun uu____11587  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____11513
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____11612 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____11618 =
              let uu____11625 =
                let uu____11626 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____11626
                 in
              new_uvar "uvar_env.2" env uu____11625  in
            bind uu____11618
              (fun uu____11643  ->
                 match uu____11643 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____11612
        (fun typ  ->
           let uu____11655 = new_uvar "uvar_env" env typ  in
           bind uu____11655
             (fun uu____11670  ->
                match uu____11670 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____11689 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____11708 -> g.FStar_Tactics_Types.opts
             | uu____11711 -> FStar_Options.peek ()  in
           let uu____11714 = FStar_Syntax_Util.head_and_args t  in
           match uu____11714 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____11734);
                FStar_Syntax_Syntax.pos = uu____11735;
                FStar_Syntax_Syntax.vars = uu____11736;_},uu____11737)
               ->
               let env1 =
                 let uu___1675_11779 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___1675_11779.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___1675_11779.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___1675_11779.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___1675_11779.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___1675_11779.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___1675_11779.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___1675_11779.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___1675_11779.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___1675_11779.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___1675_11779.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___1675_11779.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___1675_11779.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___1675_11779.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___1675_11779.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___1675_11779.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___1675_11779.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___1675_11779.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___1675_11779.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___1675_11779.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___1675_11779.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___1675_11779.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___1675_11779.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___1675_11779.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___1675_11779.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___1675_11779.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___1675_11779.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___1675_11779.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___1675_11779.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___1675_11779.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___1675_11779.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___1675_11779.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___1675_11779.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___1675_11779.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___1675_11779.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___1675_11779.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___1675_11779.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___1675_11779.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___1675_11779.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___1675_11779.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___1675_11779.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___1675_11779.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___1675_11779.FStar_TypeChecker_Env.nbe)
                 }  in
               let g =
                 FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false ""  in
               let uu____11783 =
                 let uu____11786 = bnorm_goal g  in [uu____11786]  in
               add_goals uu____11783
           | uu____11787 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____11689
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____11849 = if b then t2 else ret false  in
             bind uu____11849 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____11875 = trytac comp  in
      bind uu____11875
        (fun uu___4_11887  ->
           match uu___4_11887 with
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
        let uu____11929 =
          bind get
            (fun ps  ->
               let uu____11937 = __tc e t1  in
               bind uu____11937
                 (fun uu____11958  ->
                    match uu____11958 with
                    | (t11,ty1,g1) ->
                        let uu____11971 = __tc e t2  in
                        bind uu____11971
                          (fun uu____11992  ->
                             match uu____11992 with
                             | (t21,ty2,g2) ->
                                 let uu____12005 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____12005
                                   (fun uu____12012  ->
                                      let uu____12013 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____12013
                                        (fun uu____12021  ->
                                           let uu____12022 =
                                             do_unify e ty1 ty2  in
                                           let uu____12026 =
                                             do_unify e t11 t21  in
                                           tac_and uu____12022 uu____12026)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____11929
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____12074  ->
             let uu____12075 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____12075
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
        (fun uu____12109  ->
           let uu____12110 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____12110)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____12121 =
      mlog
        (fun uu____12126  ->
           let uu____12127 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____12127)
        (fun uu____12132  ->
           let uu____12133 = cur_goal ()  in
           bind uu____12133
             (fun g  ->
                let uu____12139 =
                  let uu____12148 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____12148 ty  in
                bind uu____12139
                  (fun uu____12160  ->
                     match uu____12160 with
                     | (ty1,uu____12170,guard) ->
                         let uu____12172 =
                           let uu____12175 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____12175 guard  in
                         bind uu____12172
                           (fun uu____12179  ->
                              let uu____12180 =
                                let uu____12184 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____12185 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____12184 uu____12185 ty1  in
                              bind uu____12180
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____12194 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____12194
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops]  in
                                      let ng =
                                        let uu____12201 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____12202 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____12201
                                          uu____12202
                                         in
                                      let nty =
                                        let uu____12204 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____12204 ty1  in
                                      let uu____12205 =
                                        let uu____12209 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____12209 ng nty  in
                                      bind uu____12205
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____12218 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____12218
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____12121
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list tac)
  =
  fun s_tm  ->
    let uu____12292 =
      let uu____12301 = cur_goal ()  in
      bind uu____12301
        (fun g  ->
           let uu____12313 =
             let uu____12322 = FStar_Tactics_Types.goal_env g  in
             __tc uu____12322 s_tm  in
           bind uu____12313
             (fun uu____12340  ->
                match uu____12340 with
                | (s_tm1,s_ty,guard) ->
                    let uu____12358 =
                      let uu____12361 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____12361 guard  in
                    bind uu____12358
                      (fun uu____12374  ->
                         let uu____12375 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____12375 with
                         | (h,args) ->
                             let uu____12420 =
                               let uu____12427 =
                                 let uu____12428 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____12428.FStar_Syntax_Syntax.n  in
                               match uu____12427 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12443;
                                      FStar_Syntax_Syntax.vars = uu____12444;_},us)
                                   -> ret (fv, us)
                               | uu____12454 -> fail "type is not an fv"  in
                             bind uu____12420
                               (fun uu____12475  ->
                                  match uu____12475 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____12491 =
                                        let uu____12494 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____12494 t_lid
                                         in
                                      (match uu____12491 with
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
                                                  (fun uu____12545  ->
                                                     let uu____12546 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____12546 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____12561 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____12589
                                                                  =
                                                                  let uu____12592
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____12592
                                                                    c_lid
                                                                   in
                                                                match uu____12589
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
                                                                    uu____12666
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
                                                                    let uu____12671
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____12671
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____12694
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____12694
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____12737
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____12737
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____12810
                                                                    =
                                                                    let uu____12812
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____12812
                                                                     in
                                                                    failwhen
                                                                    uu____12810
                                                                    "not total?"
                                                                    (fun
                                                                    uu____12831
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
                                                                    uu___5_12848
                                                                    =
                                                                    match uu___5_12848
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____12852)
                                                                    -> true
                                                                    | 
                                                                    uu____12855
                                                                    -> false
                                                                     in
                                                                    let uu____12859
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____12859
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
                                                                    uu____12993
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
                                                                    uu____13055
                                                                     ->
                                                                    match uu____13055
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13075),
                                                                    (t,uu____13077))
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
                                                                    uu____13147
                                                                     ->
                                                                    match uu____13147
                                                                    with
                                                                    | 
                                                                    ((bv,uu____13174),
                                                                    (t,uu____13176))
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
                                                                    uu____13235
                                                                     ->
                                                                    match uu____13235
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
                                                                    let uu____13290
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___1839_13307
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___1839_13307.FStar_TypeChecker_Env.nbe)
                                                                    }) s_ty
                                                                    pat  in
                                                                    match uu____13290
                                                                    with
                                                                    | 
                                                                    (uu____13321,uu____13322,uu____13323,pat_t,uu____13325,_guard_pat)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____13332
                                                                    =
                                                                    let uu____13333
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____13333
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____13332
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____13338
                                                                    =
                                                                    let uu____13347
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____13347]
                                                                     in
                                                                    let uu____13366
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____13338
                                                                    uu____13366
                                                                     in
                                                                    let nty =
                                                                    let uu____13372
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____13372
                                                                     in
                                                                    let uu____13375
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____13375
                                                                    (fun
                                                                    uu____13405
                                                                     ->
                                                                    match uu____13405
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
                                                                    let uu____13432
                                                                    =
                                                                    let uu____13443
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____13443]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____13432
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____13479
                                                                    =
                                                                    let uu____13490
                                                                    =
                                                                    let uu____13495
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____13495)
                                                                     in
                                                                    (g', br,
                                                                    uu____13490)
                                                                     in
                                                                    ret
                                                                    uu____13479))))))
                                                                    | 
                                                                    uu____13516
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____12561
                                                           (fun goal_brs  ->
                                                              let uu____13566
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____13566
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
                                                                  let uu____13639
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____13639
                                                                    (
                                                                    fun
                                                                    uu____13650
                                                                     ->
                                                                    let uu____13651
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____13651
                                                                    (fun
                                                                    uu____13661
                                                                     ->
                                                                    ret infos))))
                                            | uu____13668 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____12292
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____13717::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____13747 = init xs  in x :: uu____13747
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____13760 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____13769) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____13835 = last args  in
          (match uu____13835 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____13865 =
                 let uu____13866 =
                   let uu____13871 =
                     let uu____13872 =
                       let uu____13877 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____13877  in
                     uu____13872 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____13871, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____13866  in
               FStar_All.pipe_left ret uu____13865)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____13888,uu____13889) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____13942 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____13942 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____13984 =
                      let uu____13985 =
                        let uu____13990 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____13990)  in
                      FStar_Reflection_Data.Tv_Abs uu____13985  in
                    FStar_All.pipe_left ret uu____13984))
      | FStar_Syntax_Syntax.Tm_type uu____13993 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____14018 ->
          let uu____14033 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____14033 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____14064 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____14064 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____14117 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____14130 =
            let uu____14131 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____14131  in
          FStar_All.pipe_left ret uu____14130
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____14152 =
            let uu____14153 =
              let uu____14158 =
                let uu____14159 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____14159  in
              (uu____14158, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____14153  in
          FStar_All.pipe_left ret uu____14152
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____14199 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____14204 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____14204 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____14257 ->
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
             | FStar_Util.Inr uu____14299 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____14303 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____14303 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14323 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____14329 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____14384 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____14384
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____14405 =
                  let uu____14412 =
                    FStar_List.map
                      (fun uu____14425  ->
                         match uu____14425 with
                         | (p1,uu____14434) -> inspect_pat p1) ps
                     in
                  (fv, uu____14412)  in
                FStar_Reflection_Data.Pat_Cons uu____14405
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
              (fun uu___6_14530  ->
                 match uu___6_14530 with
                 | (pat,uu____14552,t5) ->
                     let uu____14570 = inspect_pat pat  in (uu____14570, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____14579 ->
          ((let uu____14581 =
              let uu____14587 =
                let uu____14589 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____14591 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____14589 uu____14591
                 in
              (FStar_Errors.Warning_CantInspect, uu____14587)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____14581);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____13760
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____14609 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____14609
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____14613 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____14613
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____14617 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____14617
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____14624 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____14624
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____14649 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____14649
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____14666 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____14666
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____14685 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____14685
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____14689 =
          let uu____14690 =
            let uu____14697 =
              let uu____14698 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____14698  in
            FStar_Syntax_Syntax.mk uu____14697  in
          uu____14690 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14689
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____14703 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14703
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14714 =
          let uu____14715 =
            let uu____14722 =
              let uu____14723 =
                let uu____14737 =
                  let uu____14740 =
                    let uu____14741 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____14741]  in
                  FStar_Syntax_Subst.close uu____14740 t2  in
                ((false, [lb]), uu____14737)  in
              FStar_Syntax_Syntax.Tm_let uu____14723  in
            FStar_Syntax_Syntax.mk uu____14722  in
          uu____14715 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____14714
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____14783 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____14783 with
         | (lbs,body) ->
             let uu____14798 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____14798)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____14835 =
                let uu____14836 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____14836  in
              FStar_All.pipe_left wrap uu____14835
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____14843 =
                let uu____14844 =
                  let uu____14858 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____14876 = pack_pat p1  in
                         (uu____14876, false)) ps
                     in
                  (fv, uu____14858)  in
                FStar_Syntax_Syntax.Pat_cons uu____14844  in
              FStar_All.pipe_left wrap uu____14843
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
            (fun uu___7_14925  ->
               match uu___7_14925 with
               | (pat,t1) ->
                   let uu____14942 = pack_pat pat  in
                   (uu____14942, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____14990 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____14990
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____15018 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15018
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____15064 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15064
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____15103 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____15103
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____15123 =
        bind get
          (fun ps  ->
             let uu____15129 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____15129 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____15123
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____15163 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___2137_15170 = ps  in
                 let uu____15171 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___2137_15170.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___2137_15170.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___2137_15170.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___2137_15170.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___2137_15170.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___2137_15170.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___2137_15170.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___2137_15170.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___2137_15170.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___2137_15170.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___2137_15170.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___2137_15170.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____15171
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____15163
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal * FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun typ  ->
      let uu____15198 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____15198 with
      | (u,ctx_uvars,g_u) ->
          let uu____15231 = FStar_List.hd ctx_uvars  in
          (match uu____15231 with
           | (ctx_uvar,uu____15245) ->
               let g =
                 let uu____15247 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____15247 false
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
        let uu____15270 = goal_of_goal_ty env typ  in
        match uu____15270 with
        | (g,g_u) ->
            let ps =
              let uu____15282 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____15285 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____15282;
                FStar_Tactics_Types.local_state = uu____15285
              }  in
            let uu____15295 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____15295)
  