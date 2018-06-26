open Prims
type goal = FStar_Tactics_Types.goal
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (normalize :
  FStar_TypeChecker_Normalize.step Prims.list ->
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
      try t.tac_f p
      with
      | e ->
          let uu____168 =
            let uu____173 = FStar_Util.message_of_exn e  in (uu____173, p)
             in
          FStar_Tactics_Result.Failed uu____168
  
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
           let uu____245 = run t1 p  in
           match uu____245 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____252 = t2 a  in run uu____252 q
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
    let uu____272 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____272 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____290 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____291 =
      let uu____292 = check_goal_solved g  in
      match uu____292 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____296 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____296
       in
    FStar_Util.format2 "%s%s" uu____290 uu____291
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____307 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____307
      then goal_to_string_verbose g
      else
        (let w =
           let uu____310 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____310 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____314 = FStar_Tactics_Types.goal_env g  in
               tts uu____314 t
            in
         let uu____315 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____316 =
           let uu____317 = FStar_Tactics_Types.goal_env g  in
           tts uu____317
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____315 w uu____316)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____333 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____333
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____349 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____349
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____370 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____370
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____377) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____387) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____402 =
      let uu____407 =
        let uu____408 = FStar_Tactics_Types.goal_env g  in
        let uu____409 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____408 uu____409  in
      FStar_Syntax_Util.un_squash uu____407  in
    match uu____402 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____415 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____443 =
            let uu____444 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____444  in
          if uu____443 then tacprint msg else ());
         ret ())
  
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
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____781 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____781 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
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
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
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
                 let uu___348_1033 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___348_1033.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___348_1033.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___348_1033.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___348_1033.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___348_1033.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___348_1033.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___348_1033.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___348_1033.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___348_1033.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___348_1033.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___348_1033.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1060 = trytac' t  in
    bind uu____1060
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1087 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1123 = trytac t  in run uu____1123 ps
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
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1226 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1226
         then
           let uu____1227 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1228 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1227
             uu____1228
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1240 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1240
            then
              let uu____1241 = FStar_Util.string_of_bool res  in
              let uu____1242 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1243 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1241 uu____1242 uu____1243
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1251,msg) ->
             mlog
               (fun uu____1254  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1256  -> ret false)
         | FStar_Errors.Error (uu____1257,msg,r) ->
             mlog
               (fun uu____1262  ->
                  let uu____1263 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1263) (fun uu____1265  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1288  ->
             (let uu____1290 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1290
              then
                (FStar_Options.push ();
                 (let uu____1292 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1294 = __do_unify env t1 t2  in
              bind uu____1294
                (fun r  ->
                   (let uu____1301 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1301 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___353_1309 = ps  in
         let uu____1310 =
           FStar_List.filter
             (fun g  ->
                let uu____1316 = check_goal_solved g  in
                FStar_Option.isNone uu____1316) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___353_1309.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___353_1309.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___353_1309.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1310;
           FStar_Tactics_Types.smt_goals =
             (uu___353_1309.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___353_1309.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___353_1309.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___353_1309.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___353_1309.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___353_1309.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___353_1309.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___353_1309.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1333 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1333 with
      | FStar_Pervasives_Native.Some uu____1338 ->
          let uu____1339 =
            let uu____1340 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1340  in
          fail uu____1339
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1356 = FStar_Tactics_Types.goal_env goal  in
      let uu____1357 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1356 solution uu____1357
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1363 =
         let uu___354_1364 = p  in
         let uu____1365 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_1364.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___354_1364.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___354_1364.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1365;
           FStar_Tactics_Types.smt_goals =
             (uu___354_1364.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_1364.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_1364.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_1364.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_1364.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_1364.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_1364.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_1364.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1363)
  
let (dismiss : unit -> unit tac) =
  fun uu____1374  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1381 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1402  ->
           let uu____1403 =
             let uu____1404 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1404  in
           let uu____1405 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1403 uu____1405)
        (fun uu____1408  ->
           let uu____1409 = trysolve goal solution  in
           bind uu____1409
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1417  -> remove_solved_goals)
                else
                  (let uu____1419 =
                     let uu____1420 =
                       let uu____1421 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1421 solution  in
                     let uu____1422 =
                       let uu____1423 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1424 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1423 uu____1424  in
                     let uu____1425 =
                       let uu____1426 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1427 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1426 uu____1427  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1420 uu____1422 uu____1425
                      in
                   fail uu____1419)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1442 = set_solution goal solution  in
      bind uu____1442
        (fun uu____1446  ->
           bind __dismiss (fun uu____1448  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___355_1455 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___355_1455.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___355_1455.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___355_1455.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___355_1455.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___355_1455.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___355_1455.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___355_1455.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___355_1455.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___355_1455.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___355_1455.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___355_1455.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1474 = FStar_Options.defensive ()  in
    if uu____1474
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1479 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1479)
         in
      let b2 =
        b1 &&
          (let uu____1482 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1482)
         in
      let rec aux b3 e =
        let uu____1494 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1494 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1512 =
        (let uu____1515 = aux b2 env  in Prims.op_Negation uu____1515) &&
          (let uu____1517 = FStar_ST.op_Bang nwarn  in
           uu____1517 < (Prims.parse_int "5"))
         in
      (if uu____1512
       then
         ((let uu____1538 =
             let uu____1539 = FStar_Tactics_Types.goal_type g  in
             uu____1539.FStar_Syntax_Syntax.pos  in
           let uu____1542 =
             let uu____1547 =
               let uu____1548 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1548
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1547)  in
           FStar_Errors.log_issue uu____1538 uu____1542);
          (let uu____1549 =
             let uu____1550 = FStar_ST.op_Bang nwarn  in
             uu____1550 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1549))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___356_1610 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___356_1610.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___356_1610.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___356_1610.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___356_1610.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___356_1610.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___356_1610.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___356_1610.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___356_1610.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___356_1610.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___356_1610.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___356_1610.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1630 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1630.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1630.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1630.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___357_1630.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_1630.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1630.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1630.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1630.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1630.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1630.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1630.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_1650 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1650.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1650.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_1650.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___358_1650.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_1650.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1650.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1650.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1650.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1650.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1650.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1650.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___359_1670 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1670.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1670.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_1670.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1670.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___359_1670.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1670.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1670.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1670.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1670.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1670.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1670.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1681  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___360_1695 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1695.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1695.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1695.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1695.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1695.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1695.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1695.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1695.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1695.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1695.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1695.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
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
        let uu____1723 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1723 with
        | (u,ctx_uvar,g_u) ->
            let uu____1757 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1757
              (fun uu____1766  ->
                 let uu____1767 =
                   let uu____1772 =
                     let uu____1773 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1773  in
                   (u, uu____1772)  in
                 ret uu____1767)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1791 = FStar_Syntax_Util.un_squash t  in
    match uu____1791 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1801 =
          let uu____1802 = FStar_Syntax_Subst.compress t'  in
          uu____1802.FStar_Syntax_Syntax.n  in
        (match uu____1801 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1806 -> false)
    | uu____1807 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1817 = FStar_Syntax_Util.un_squash t  in
    match uu____1817 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1827 =
          let uu____1828 = FStar_Syntax_Subst.compress t'  in
          uu____1828.FStar_Syntax_Syntax.n  in
        (match uu____1827 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1832 -> false)
    | uu____1833 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1844  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1855 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1855 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1862 = goal_to_string_verbose hd1  in
                    let uu____1863 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1862 uu____1863);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1870  ->
    let uu____1873 =
      bind get
        (fun ps  ->
           let uu____1879 = cur_goal ()  in
           bind uu____1879
             (fun g  ->
                (let uu____1886 =
                   let uu____1887 = FStar_Tactics_Types.goal_type g  in
                   uu____1887.FStar_Syntax_Syntax.pos  in
                 let uu____1890 =
                   let uu____1895 =
                     let uu____1896 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1896
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1895)  in
                 FStar_Errors.log_issue uu____1886 uu____1890);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1873
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1907  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___361_1917 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___361_1917.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___361_1917.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___361_1917.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___361_1917.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___361_1917.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___361_1917.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___361_1917.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___361_1917.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___361_1917.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___361_1917.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___361_1917.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1918 = set ps1  in
         bind uu____1918
           (fun uu____1923  ->
              let uu____1924 = FStar_BigInt.of_int_fs n1  in ret uu____1924))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1931  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1939 = FStar_BigInt.of_int_fs n1  in ret uu____1939)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1952  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1960 = FStar_BigInt.of_int_fs n1  in ret uu____1960)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1973  ->
    let uu____1976 = cur_goal ()  in
    bind uu____1976 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2008 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2008 phi  in
          let uu____2009 = new_uvar reason env typ  in
          bind uu____2009
            (fun uu____2024  ->
               match uu____2024 with
               | (uu____2031,ctx_uvar) ->
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
             (fun uu____2076  ->
                let uu____2077 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2077)
             (fun uu____2080  ->
                let e1 =
                  let uu___362_2082 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___362_2082.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___362_2082.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___362_2082.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___362_2082.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___362_2082.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___362_2082.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___362_2082.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___362_2082.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___362_2082.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___362_2082.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___362_2082.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___362_2082.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___362_2082.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___362_2082.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___362_2082.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___362_2082.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___362_2082.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___362_2082.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___362_2082.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___362_2082.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___362_2082.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___362_2082.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___362_2082.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___362_2082.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___362_2082.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___362_2082.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___362_2082.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___362_2082.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___362_2082.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___362_2082.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___362_2082.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___362_2082.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___362_2082.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___362_2082.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___362_2082.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___362_2082.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___362_2082.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___362_2082.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___362_2082.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___362_2082.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2102 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2102
                with
                | FStar_Errors.Err (uu____2129,msg) ->
                    let uu____2131 = tts e1 t  in
                    let uu____2132 =
                      let uu____2133 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2133
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2131 uu____2132 msg
                | FStar_Errors.Error (uu____2140,msg,uu____2142) ->
                    let uu____2143 = tts e1 t  in
                    let uu____2144 =
                      let uu____2145 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2145
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2143 uu____2144 msg))
  
let (istrivial : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Normalize.Reify;
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Normalize.Primops;
        FStar_TypeChecker_Normalize.Simplify;
        FStar_TypeChecker_Normalize.UnfoldTac;
        FStar_TypeChecker_Normalize.Unmeta]  in
      let t1 = normalize steps e t  in is_true t1
  
let (get_guard_policy : unit -> FStar_Tactics_Types.guard_policy tac) =
  fun uu____2172  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___365_2190 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___365_2190.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___365_2190.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___365_2190.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___365_2190.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___365_2190.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___365_2190.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___365_2190.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___365_2190.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___365_2190.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___365_2190.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___365_2190.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2214 = get_guard_policy ()  in
      bind uu____2214
        (fun old_pol  ->
           let uu____2220 = set_guard_policy pol  in
           bind uu____2220
             (fun uu____2224  ->
                bind t
                  (fun r  ->
                     let uu____2228 = set_guard_policy old_pol  in
                     bind uu____2228 (fun uu____2232  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2235 = let uu____2240 = cur_goal ()  in trytac uu____2240  in
  bind uu____2235
    (fun uu___338_2247  ->
       match uu___338_2247 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2253 = FStar_Options.peek ()  in ret uu____2253)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2276 =
               let uu____2277 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2277.FStar_TypeChecker_Env.guard_f  in
             match uu____2276 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2281 = istrivial e f  in
                 if uu____2281
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2289 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2289
                              (fun goal  ->
                                 let goal1 =
                                   let uu___366_2296 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___366_2296.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___366_2296.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___366_2296.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2297 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2297
                              (fun goal  ->
                                 let goal1 =
                                   let uu___367_2304 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___367_2304.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___367_2304.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___367_2304.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2312 =
                                 let uu____2313 =
                                   let uu____2314 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2314
                                    in
                                 Prims.op_Negation uu____2313  in
                               if uu____2312
                               then
                                 mlog
                                   (fun uu____2319  ->
                                      let uu____2320 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2320)
                                   (fun uu____2322  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2329 ->
                                 mlog
                                   (fun uu____2332  ->
                                      let uu____2333 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2333)
                                   (fun uu____2335  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2345 =
      let uu____2348 = cur_goal ()  in
      bind uu____2348
        (fun goal  ->
           let uu____2354 =
             let uu____2363 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2363 t  in
           bind uu____2354
             (fun uu____2375  ->
                match uu____2375 with
                | (t1,typ,guard) ->
                    let uu____2387 =
                      let uu____2390 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2390 guard  in
                    bind uu____2387 (fun uu____2392  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2345
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2421 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2421 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2432  ->
    let uu____2435 = cur_goal ()  in
    bind uu____2435
      (fun goal  ->
         let uu____2441 =
           let uu____2442 = FStar_Tactics_Types.goal_env goal  in
           let uu____2443 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2442 uu____2443  in
         if uu____2441
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2447 =
              let uu____2448 = FStar_Tactics_Types.goal_env goal  in
              let uu____2449 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2448 uu____2449  in
            fail1 "Not a trivial goal: %s" uu____2447))
  
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
          let uu____2478 =
            let uu____2479 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2479.FStar_TypeChecker_Env.guard_f  in
          match uu____2478 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2487 = istrivial e f  in
              if uu____2487
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2495 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2495
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___370_2505 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___370_2505.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___370_2505.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___370_2505.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2512  ->
    let uu____2515 = cur_goal ()  in
    bind uu____2515
      (fun g  ->
         let uu____2521 = is_irrelevant g  in
         if uu____2521
         then bind __dismiss (fun uu____2525  -> add_smt_goals [g])
         else
           (let uu____2527 =
              let uu____2528 = FStar_Tactics_Types.goal_env g  in
              let uu____2529 = FStar_Tactics_Types.goal_type g  in
              tts uu____2528 uu____2529  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2527))
  
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
             let uu____2578 =
               try
                 let uu____2612 =
                   let uu____2621 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2621 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2612
               with | uu____2643 -> fail "divide: not enough goals"  in
             bind uu____2578
               (fun uu____2669  ->
                  match uu____2669 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___371_2695 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___371_2695.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___371_2695.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___371_2695.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___371_2695.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___371_2695.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___371_2695.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___371_2695.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___371_2695.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___371_2695.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___371_2695.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2696 = set lp  in
                      bind uu____2696
                        (fun uu____2704  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___372_2720 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___372_2720.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___372_2720.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___372_2720.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___372_2720.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___372_2720.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___372_2720.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___372_2720.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___372_2720.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___372_2720.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___372_2720.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2721 = set rp  in
                                     bind uu____2721
                                       (fun uu____2729  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___373_2745 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___373_2745.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___373_2745.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2746 = set p'
                                                       in
                                                    bind uu____2746
                                                      (fun uu____2754  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2760 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2781 = divide FStar_BigInt.one f idtac  in
    bind uu____2781
      (fun uu____2794  -> match uu____2794 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2831::uu____2832 ->
             let uu____2835 =
               let uu____2844 = map tau  in
               divide FStar_BigInt.one tau uu____2844  in
             bind uu____2835
               (fun uu____2862  ->
                  match uu____2862 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2903 =
        bind t1
          (fun uu____2908  ->
             let uu____2909 = map t2  in
             bind uu____2909 (fun uu____2917  -> ret ()))
         in
      focus uu____2903
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2926  ->
    let uu____2929 =
      let uu____2932 = cur_goal ()  in
      bind uu____2932
        (fun goal  ->
           let uu____2941 =
             let uu____2948 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2948  in
           match uu____2941 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2957 =
                 let uu____2958 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2958  in
               if uu____2957
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2963 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2963 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2977 = new_uvar "intro" env' typ'  in
                  bind uu____2977
                    (fun uu____2993  ->
                       match uu____2993 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3017 = set_solution goal sol  in
                           bind uu____3017
                             (fun uu____3023  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3025 =
                                  let uu____3028 = bnorm_goal g  in
                                  replace_cur uu____3028  in
                                bind uu____3025 (fun uu____3030  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3035 =
                 let uu____3036 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3037 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3036 uu____3037  in
               fail1 "goal is not an arrow (%s)" uu____3035)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2929
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3052  ->
    let uu____3059 = cur_goal ()  in
    bind uu____3059
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3076 =
            let uu____3083 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3083  in
          match uu____3076 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3096 =
                let uu____3097 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3097  in
              if uu____3096
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3110 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3110
                    in
                 let bs =
                   let uu____3120 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3120; b]  in
                 let env' =
                   let uu____3146 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3146 bs  in
                 let uu____3147 =
                   let uu____3154 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3154  in
                 bind uu____3147
                   (fun uu____3173  ->
                      match uu____3173 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3187 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3190 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3187
                              FStar_Parser_Const.effect_Tot_lid uu____3190 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3208 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3208 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3230 =
                                   let uu____3231 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3231.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3230
                                  in
                               let uu____3244 = set_solution goal tm  in
                               bind uu____3244
                                 (fun uu____3253  ->
                                    let uu____3254 =
                                      let uu____3257 =
                                        bnorm_goal
                                          (let uu___376_3260 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___376_3260.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___376_3260.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___376_3260.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3257  in
                                    bind uu____3254
                                      (fun uu____3267  ->
                                         let uu____3268 =
                                           let uu____3273 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3273, b)  in
                                         ret uu____3268)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3282 =
                let uu____3283 = FStar_Tactics_Types.goal_env goal  in
                let uu____3284 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3283 uu____3284  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3282))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3302 = cur_goal ()  in
    bind uu____3302
      (fun goal  ->
         mlog
           (fun uu____3309  ->
              let uu____3310 =
                let uu____3311 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3311  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3310)
           (fun uu____3316  ->
              let steps =
                let uu____3320 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3320
                 in
              let t =
                let uu____3324 = FStar_Tactics_Types.goal_env goal  in
                let uu____3325 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3324 uu____3325  in
              let uu____3326 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3326))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3350 =
          mlog
            (fun uu____3355  ->
               let uu____3356 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3356)
            (fun uu____3358  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3364 -> g.FStar_Tactics_Types.opts
                      | uu____3367 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3372  ->
                         let uu____3373 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3373)
                      (fun uu____3376  ->
                         let uu____3377 = __tc e t  in
                         bind uu____3377
                           (fun uu____3398  ->
                              match uu____3398 with
                              | (t1,uu____3408,uu____3409) ->
                                  let steps =
                                    let uu____3413 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3413
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3350
  
let (refine_intro : unit -> unit tac) =
  fun uu____3427  ->
    let uu____3430 =
      let uu____3433 = cur_goal ()  in
      bind uu____3433
        (fun g  ->
           let uu____3440 =
             let uu____3451 = FStar_Tactics_Types.goal_env g  in
             let uu____3452 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3451 uu____3452
              in
           match uu____3440 with
           | (uu____3455,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3480 =
                 let uu____3485 =
                   let uu____3490 =
                     let uu____3491 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3491]  in
                   FStar_Syntax_Subst.open_term uu____3490 phi  in
                 match uu____3485 with
                 | (bvs,phi1) ->
                     let uu____3516 =
                       let uu____3517 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3517  in
                     (uu____3516, phi1)
                  in
               (match uu____3480 with
                | (bv1,phi1) ->
                    let uu____3536 =
                      let uu____3539 = FStar_Tactics_Types.goal_env g  in
                      let uu____3540 =
                        let uu____3541 =
                          let uu____3544 =
                            let uu____3545 =
                              let uu____3552 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3552)  in
                            FStar_Syntax_Syntax.NT uu____3545  in
                          [uu____3544]  in
                        FStar_Syntax_Subst.subst uu____3541 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3539
                        uu____3540 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3536
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3560  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3430
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3579 = cur_goal ()  in
      bind uu____3579
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3587 = FStar_Tactics_Types.goal_env goal  in
               let uu____3588 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3587 uu____3588
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3590 = __tc env t  in
           bind uu____3590
             (fun uu____3609  ->
                match uu____3609 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3624  ->
                         let uu____3625 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3626 =
                           let uu____3627 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3627
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3625 uu____3626)
                      (fun uu____3630  ->
                         let uu____3631 =
                           let uu____3634 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3634 guard  in
                         bind uu____3631
                           (fun uu____3636  ->
                              mlog
                                (fun uu____3640  ->
                                   let uu____3641 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3642 =
                                     let uu____3643 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3643
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3641 uu____3642)
                                (fun uu____3646  ->
                                   let uu____3647 =
                                     let uu____3650 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3651 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3650 typ uu____3651  in
                                   bind uu____3647
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3657 =
                                             let uu____3658 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3658 t1  in
                                           let uu____3659 =
                                             let uu____3660 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3660 typ  in
                                           let uu____3661 =
                                             let uu____3662 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3663 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3662 uu____3663  in
                                           let uu____3664 =
                                             let uu____3665 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3666 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3665 uu____3666  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3657 uu____3659 uu____3661
                                             uu____3664)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3681 =
        mlog
          (fun uu____3686  ->
             let uu____3687 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3687)
          (fun uu____3690  ->
             let uu____3691 =
               let uu____3698 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3698  in
             bind uu____3691
               (fun uu___340_3707  ->
                  match uu___340_3707 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3717  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3720  ->
                           let uu____3721 =
                             let uu____3728 =
                               let uu____3731 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3731
                                 (fun uu____3736  ->
                                    let uu____3737 = refine_intro ()  in
                                    bind uu____3737
                                      (fun uu____3741  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3728  in
                           bind uu____3721
                             (fun uu___339_3748  ->
                                match uu___339_3748 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3756 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3681
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3806 = f x  in
          bind uu____3806
            (fun y  ->
               let uu____3814 = mapM f xs  in
               bind uu____3814 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3885 = do_unify e ty1 ty2  in
          bind uu____3885
            (fun uu___341_3897  ->
               if uu___341_3897
               then ret acc
               else
                 (let uu____3916 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3916 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3937 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3938 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3937
                        uu____3938
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3953 =
                        let uu____3954 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3954  in
                      if uu____3953
                      then fail "Codomain is effectful"
                      else
                        (let uu____3974 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3974
                           (fun uu____4000  ->
                              match uu____4000 with
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
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4086 =
        mlog
          (fun uu____4091  ->
             let uu____4092 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4092)
          (fun uu____4095  ->
             let uu____4096 = cur_goal ()  in
             bind uu____4096
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4104 = __tc e tm  in
                  bind uu____4104
                    (fun uu____4125  ->
                       match uu____4125 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4138 =
                             let uu____4149 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4149  in
                           bind uu____4138
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4192  ->
                                       fun w  ->
                                         match uu____4192 with
                                         | (uvt,q,uu____4210) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4242 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4259  ->
                                       fun s  ->
                                         match uu____4259 with
                                         | (uu____4271,uu____4272,uv) ->
                                             let uu____4274 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4274) uvs uu____4242
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4283 = solve' goal w  in
                                bind uu____4283
                                  (fun uu____4288  ->
                                     let uu____4289 =
                                       mapM
                                         (fun uu____4306  ->
                                            match uu____4306 with
                                            | (uvt,q,uv) ->
                                                let uu____4318 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4318 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4323 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4324 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4324
                                                     then ret ()
                                                     else
                                                       (let uu____4328 =
                                                          let uu____4331 =
                                                            bnorm_goal
                                                              (let uu___377_4334
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___377_4334.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___377_4334.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4331]  in
                                                        add_goals uu____4328)))
                                         uvs
                                        in
                                     bind uu____4289
                                       (fun uu____4338  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4086
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4363 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4363
    then
      let uu____4370 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4385 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4438 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4370 with
      | (pre,post) ->
          let post1 =
            let uu____4470 =
              let uu____4481 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4481]  in
            FStar_Syntax_Util.mk_app post uu____4470  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4511 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4511
       then
         let uu____4518 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4518
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4551 =
      let uu____4554 =
        mlog
          (fun uu____4559  ->
             let uu____4560 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4560)
          (fun uu____4564  ->
             let is_unit_t t =
               let uu____4571 =
                 let uu____4572 = FStar_Syntax_Subst.compress t  in
                 uu____4572.FStar_Syntax_Syntax.n  in
               match uu____4571 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4576 -> false  in
             let uu____4577 = cur_goal ()  in
             bind uu____4577
               (fun goal  ->
                  let uu____4583 =
                    let uu____4592 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4592 tm  in
                  bind uu____4583
                    (fun uu____4607  ->
                       match uu____4607 with
                       | (tm1,t,guard) ->
                           let uu____4619 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4619 with
                            | (bs,comp) ->
                                let uu____4652 = lemma_or_sq comp  in
                                (match uu____4652 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4671 =
                                       FStar_List.fold_left
                                         (fun uu____4719  ->
                                            fun uu____4720  ->
                                              match (uu____4719, uu____4720)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4833 =
                                                    is_unit_t b_t  in
                                                  if uu____4833
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4871 =
                                                       let uu____4884 =
                                                         let uu____4885 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4885.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4888 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4884
                                                         uu____4888 b_t
                                                        in
                                                     match uu____4871 with
                                                     | (u,uu____4906,g_u) ->
                                                         let uu____4920 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4920,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4671 with
                                      | (uvs,implicits,subst1) ->
                                          let uvs1 = FStar_List.rev uvs  in
                                          let pre1 =
                                            FStar_Syntax_Subst.subst subst1
                                              pre
                                             in
                                          let post1 =
                                            FStar_Syntax_Subst.subst subst1
                                              post
                                             in
                                          let uu____4999 =
                                            let uu____5002 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____5003 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____5004 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____5002 uu____5003
                                              uu____5004
                                             in
                                          bind uu____4999
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____5012 =
                                                   let uu____5013 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____5013 tm1  in
                                                 let uu____5014 =
                                                   let uu____5015 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5016 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____5015 uu____5016
                                                    in
                                                 let uu____5017 =
                                                   let uu____5018 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5019 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____5018 uu____5019
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____5012 uu____5014
                                                   uu____5017
                                               else
                                                 (let uu____5021 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____5021
                                                    (fun uu____5026  ->
                                                       let uu____5027 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____5027
                                                         (fun uu____5035  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____5060
                                                                  =
                                                                  let uu____5063
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____5063
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____5060
                                                                 in
                                                              FStar_List.existsML
                                                                (fun u  ->
                                                                   FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                free_uvars
                                                               in
                                                            let appears uv
                                                              goals =
                                                              FStar_List.existsML
                                                                (fun g'  ->
                                                                   let uu____5098
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5098)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5114
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5114
                                                              with
                                                              | (hd1,uu____5132)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5158)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5175
                                                                    -> false)
                                                               in
                                                            let uu____5176 =
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
                                                                    let uu____5224
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5224
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5252)
                                                                    ->
                                                                    let uu____5277
                                                                    =
                                                                    let uu____5278
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5278.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5277
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5292)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___378_5312
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___378_5312.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___378_5312.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___378_5312.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5325
                                                                    ->
                                                                    let env =
                                                                    let uu___379_5327
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___379_5327.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5329
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5329
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____5332
                                                                    =
                                                                    let uu____5339
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5339
                                                                    term1  in
                                                                    match uu____5332
                                                                    with
                                                                    | 
                                                                    (uu____5340,uu____5341,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5343
                                                                    =
                                                                    let uu____5348
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5348
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5343
                                                                    (fun
                                                                    uu___342_5360
                                                                     ->
                                                                    match uu___342_5360
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    ret
                                                                    ([], [])
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g ->
                                                                    ret
                                                                    ([], [g])))))
                                                               in
                                                            bind uu____5176
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5428
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5428
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5450
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5450
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5511
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5511
                                                                    then
                                                                    let uu____5514
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5514
                                                                    else
                                                                    filter' f
                                                                    xs1
                                                                    in
                                                                 let sub_goals1
                                                                   =
                                                                   filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5528
                                                                    =
                                                                    let uu____5529
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5529
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5528)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5530
                                                                   =
                                                                   let uu____5533
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5533
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5530
                                                                   (fun
                                                                    uu____5536
                                                                     ->
                                                                    let uu____5537
                                                                    =
                                                                    let uu____5540
                                                                    =
                                                                    let uu____5541
                                                                    =
                                                                    let uu____5542
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5543
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5542
                                                                    uu____5543
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5541
                                                                     in
                                                                    if
                                                                    uu____5540
                                                                    then
                                                                    let uu____5546
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5546
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5537
                                                                    (fun
                                                                    uu____5550
                                                                     ->
                                                                    let uu____5551
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5551
                                                                    (fun
                                                                    uu____5555
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4554  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4551
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5577 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5577 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5587::(e1,uu____5589)::(e2,uu____5591)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5652 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5676 = destruct_eq' typ  in
    match uu____5676 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5706 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5706 with
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
        let uu____5768 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5768 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5816 = aux e'  in
               FStar_Util.map_opt uu____5816
                 (fun uu____5840  ->
                    match uu____5840 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5861 = aux e  in
      FStar_Util.map_opt uu____5861
        (fun uu____5885  ->
           match uu____5885 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5952 =
            let uu____5961 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5961  in
          FStar_Util.map_opt uu____5952
            (fun uu____5976  ->
               match uu____5976 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___380_5995 = bv  in
                     let uu____5996 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___380_5995.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___380_5995.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5996
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___381_6004 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6005 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6014 =
                       let uu____6017 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6017  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___381_6004.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6005;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6014;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___381_6004.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___381_6004.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___381_6004.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___382_6018 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___382_6018.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___382_6018.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___382_6018.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6028 =
      let uu____6031 = cur_goal ()  in
      bind uu____6031
        (fun goal  ->
           let uu____6039 = h  in
           match uu____6039 with
           | (bv,uu____6043) ->
               mlog
                 (fun uu____6051  ->
                    let uu____6052 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6053 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6052
                      uu____6053)
                 (fun uu____6056  ->
                    let uu____6057 =
                      let uu____6066 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6066  in
                    match uu____6057 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6087 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6087 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6102 =
                               let uu____6103 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6103.FStar_Syntax_Syntax.n  in
                             (match uu____6102 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___383_6120 = bv1  in
                                    let uu____6121 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___383_6120.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___383_6120.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6121
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___384_6129 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6130 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6139 =
                                      let uu____6142 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6142
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___384_6129.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6130;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6139;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___384_6129.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___384_6129.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___384_6129.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___385_6145 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___385_6145.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___385_6145.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___385_6145.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6146 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6147 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6028
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6172 =
        let uu____6175 = cur_goal ()  in
        bind uu____6175
          (fun goal  ->
             let uu____6186 = b  in
             match uu____6186 with
             | (bv,uu____6190) ->
                 let bv' =
                   let uu____6196 =
                     let uu___386_6197 = bv  in
                     let uu____6198 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6198;
                       FStar_Syntax_Syntax.index =
                         (uu___386_6197.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___386_6197.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6196  in
                 let s1 =
                   let uu____6202 =
                     let uu____6203 =
                       let uu____6210 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6210)  in
                     FStar_Syntax_Syntax.NT uu____6203  in
                   [uu____6202]  in
                 let uu____6215 = subst_goal bv bv' s1 goal  in
                 (match uu____6215 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6172
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6234 =
      let uu____6237 = cur_goal ()  in
      bind uu____6237
        (fun goal  ->
           let uu____6246 = b  in
           match uu____6246 with
           | (bv,uu____6250) ->
               let uu____6255 =
                 let uu____6264 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6264  in
               (match uu____6255 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6285 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6285 with
                     | (ty,u) ->
                         let uu____6294 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6294
                           (fun uu____6312  ->
                              match uu____6312 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___387_6322 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___387_6322.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___387_6322.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6326 =
                                      let uu____6327 =
                                        let uu____6334 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6334)  in
                                      FStar_Syntax_Syntax.NT uu____6327  in
                                    [uu____6326]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___388_6346 = b1  in
                                         let uu____6347 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___388_6346.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___388_6346.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6347
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6354  ->
                                       let new_goal =
                                         let uu____6356 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6357 =
                                           let uu____6358 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6358
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6356 uu____6357
                                          in
                                       let uu____6359 = add_goals [new_goal]
                                          in
                                       bind uu____6359
                                         (fun uu____6364  ->
                                            let uu____6365 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6365
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6234
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6388 =
        let uu____6391 = cur_goal ()  in
        bind uu____6391
          (fun goal  ->
             let uu____6400 = b  in
             match uu____6400 with
             | (bv,uu____6404) ->
                 let uu____6409 =
                   let uu____6418 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6418  in
                 (match uu____6409 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6442 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6442
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___389_6447 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___389_6447.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___389_6447.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6449 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6449))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6388
  
let (revert : unit -> unit tac) =
  fun uu____6460  ->
    let uu____6463 = cur_goal ()  in
    bind uu____6463
      (fun goal  ->
         let uu____6469 =
           let uu____6476 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6476  in
         match uu____6469 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6492 =
                 let uu____6495 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6495  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6492
                in
             let uu____6510 = new_uvar "revert" env' typ'  in
             bind uu____6510
               (fun uu____6525  ->
                  match uu____6525 with
                  | (r,u_r) ->
                      let uu____6534 =
                        let uu____6537 =
                          let uu____6538 =
                            let uu____6539 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6539.FStar_Syntax_Syntax.pos  in
                          let uu____6542 =
                            let uu____6547 =
                              let uu____6548 =
                                let uu____6557 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6557  in
                              [uu____6548]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6547  in
                          uu____6542 FStar_Pervasives_Native.None uu____6538
                           in
                        set_solution goal uu____6537  in
                      bind uu____6534
                        (fun uu____6578  ->
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
      let uu____6590 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6590
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6605 = cur_goal ()  in
    bind uu____6605
      (fun goal  ->
         mlog
           (fun uu____6613  ->
              let uu____6614 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6615 =
                let uu____6616 =
                  let uu____6617 =
                    let uu____6626 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6626  in
                  FStar_All.pipe_right uu____6617 FStar_List.length  in
                FStar_All.pipe_right uu____6616 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6614 uu____6615)
           (fun uu____6643  ->
              let uu____6644 =
                let uu____6653 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6653  in
              match uu____6644 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6692 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6692
                        then
                          let uu____6695 =
                            let uu____6696 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6696
                             in
                          fail uu____6695
                        else check1 bvs2
                     in
                  let uu____6698 =
                    let uu____6699 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6699  in
                  if uu____6698
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6703 = check1 bvs  in
                     bind uu____6703
                       (fun uu____6709  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6711 =
                            let uu____6718 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6718  in
                          bind uu____6711
                            (fun uu____6727  ->
                               match uu____6727 with
                               | (ut,uvar_ut) ->
                                   let uu____6736 = set_solution goal ut  in
                                   bind uu____6736
                                     (fun uu____6741  ->
                                        let uu____6742 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6742))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6749  ->
    let uu____6752 = cur_goal ()  in
    bind uu____6752
      (fun goal  ->
         let uu____6758 =
           let uu____6765 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6765  in
         match uu____6758 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6773) ->
             let uu____6778 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6778)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6788 = cur_goal ()  in
    bind uu____6788
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6798 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6798  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6801  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6811 = cur_goal ()  in
    bind uu____6811
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6821 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6821  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6824  -> add_goals [g']))
  
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
            let uu____6864 = FStar_Syntax_Subst.compress t  in
            uu____6864.FStar_Syntax_Syntax.n  in
          let uu____6867 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___393_6873 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___393_6873.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___393_6873.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6867
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6889 =
                   let uu____6890 = FStar_Syntax_Subst.compress t1  in
                   uu____6890.FStar_Syntax_Syntax.n  in
                 match uu____6889 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6921 = ff hd1  in
                     bind uu____6921
                       (fun hd2  ->
                          let fa uu____6947 =
                            match uu____6947 with
                            | (a,q) ->
                                let uu____6968 = ff a  in
                                bind uu____6968 (fun a1  -> ret (a1, q))
                             in
                          let uu____6987 = mapM fa args  in
                          bind uu____6987
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7069 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7069 with
                      | (bs1,t') ->
                          let uu____7078 =
                            let uu____7081 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7081 t'  in
                          bind uu____7078
                            (fun t''  ->
                               let uu____7085 =
                                 let uu____7086 =
                                   let uu____7105 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7114 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7105, uu____7114, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7086  in
                               ret uu____7085))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7189 = ff hd1  in
                     bind uu____7189
                       (fun hd2  ->
                          let ffb br =
                            let uu____7204 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7204 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7236 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7236  in
                                let uu____7237 = ff1 e  in
                                bind uu____7237
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7252 = mapM ffb brs  in
                          bind uu____7252
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7296;
                          FStar_Syntax_Syntax.lbtyp = uu____7297;
                          FStar_Syntax_Syntax.lbeff = uu____7298;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7300;
                          FStar_Syntax_Syntax.lbpos = uu____7301;_}::[]),e)
                     ->
                     let lb =
                       let uu____7326 =
                         let uu____7327 = FStar_Syntax_Subst.compress t1  in
                         uu____7327.FStar_Syntax_Syntax.n  in
                       match uu____7326 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7331) -> lb
                       | uu____7344 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7353 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7353
                         (fun def1  ->
                            ret
                              (let uu___390_7359 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___390_7359.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___390_7359.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___390_7359.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___390_7359.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___390_7359.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___390_7359.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7360 = fflb lb  in
                     bind uu____7360
                       (fun lb1  ->
                          let uu____7370 =
                            let uu____7375 =
                              let uu____7376 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7376]  in
                            FStar_Syntax_Subst.open_term uu____7375 e  in
                          match uu____7370 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7406 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7406  in
                              let uu____7407 = ff1 e1  in
                              bind uu____7407
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7448 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7448
                         (fun def  ->
                            ret
                              (let uu___391_7454 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___391_7454.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___391_7454.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___391_7454.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___391_7454.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___391_7454.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___391_7454.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7455 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7455 with
                      | (lbs1,e1) ->
                          let uu____7470 = mapM fflb lbs1  in
                          bind uu____7470
                            (fun lbs2  ->
                               let uu____7482 = ff e1  in
                               bind uu____7482
                                 (fun e2  ->
                                    let uu____7490 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7490 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7558 = ff t2  in
                     bind uu____7558
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7589 = ff t2  in
                     bind uu____7589
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7596 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___392_7603 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___392_7603.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___392_7603.FStar_Syntax_Syntax.vars)
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
            let uu____7640 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7640 with
            | (t1,lcomp,g) ->
                let uu____7652 =
                  (let uu____7655 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7655) ||
                    (let uu____7657 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7657)
                   in
                if uu____7652
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7665 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7665
                       (fun uu____7681  ->
                          match uu____7681 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7694  ->
                                    let uu____7695 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7696 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7695 uu____7696);
                               (let uu____7697 =
                                  let uu____7700 =
                                    let uu____7701 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7701 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7700
                                    opts
                                   in
                                bind uu____7697
                                  (fun uu____7704  ->
                                     let uu____7705 =
                                       bind tau
                                         (fun uu____7711  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7717  ->
                                                 let uu____7718 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7719 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7718 uu____7719);
                                            ret ut1)
                                        in
                                     focus uu____7705))))
                      in
                   let uu____7720 = trytac' rewrite_eq  in
                   bind uu____7720
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
          let uu____7918 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7918
            (fun t1  ->
               let uu____7926 =
                 f env
                   (let uu___396_7935 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___396_7935.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___396_7935.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7926
                 (fun uu____7951  ->
                    match uu____7951 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7974 =
                               let uu____7975 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7975.FStar_Syntax_Syntax.n  in
                             match uu____7974 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8012 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8012
                                   (fun uu____8037  ->
                                      match uu____8037 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8053 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8053
                                            (fun uu____8080  ->
                                               match uu____8080 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___394_8110 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___394_8110.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___394_8110.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8152 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8152 with
                                  | (bs1,t') ->
                                      let uu____8167 =
                                        let uu____8174 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8174 ctrl1 t'
                                         in
                                      bind uu____8167
                                        (fun uu____8192  ->
                                           match uu____8192 with
                                           | (t'',ctrl2) ->
                                               let uu____8207 =
                                                 let uu____8214 =
                                                   let uu___395_8217 = t4  in
                                                   let uu____8220 =
                                                     let uu____8221 =
                                                       let uu____8240 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8249 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8240,
                                                         uu____8249, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8221
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8220;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___395_8217.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___395_8217.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8214, ctrl2)  in
                                               ret uu____8207))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8302 -> ret (t3, ctrl1))))

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
              let uu____8349 = ctrl_tac_fold f env ctrl t  in
              bind uu____8349
                (fun uu____8373  ->
                   match uu____8373 with
                   | (t1,ctrl1) ->
                       let uu____8388 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8388
                         (fun uu____8415  ->
                            match uu____8415 with
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
              let uu____8499 =
                let uu____8506 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8506
                  (fun uu____8515  ->
                     let uu____8516 = ctrl t1  in
                     bind uu____8516
                       (fun res  ->
                          let uu____8539 = trivial ()  in
                          bind uu____8539 (fun uu____8547  -> ret res)))
                 in
              bind uu____8499
                (fun uu____8563  ->
                   match uu____8563 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8587 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8587 with
                          | (t2,lcomp,g) ->
                              let uu____8603 =
                                (let uu____8606 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8606) ||
                                  (let uu____8608 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8608)
                                 in
                              if uu____8603
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8621 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8621
                                   (fun uu____8641  ->
                                      match uu____8641 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8658  ->
                                                let uu____8659 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8660 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8659 uu____8660);
                                           (let uu____8661 =
                                              let uu____8664 =
                                                let uu____8665 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8665 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8664 opts
                                               in
                                            bind uu____8661
                                              (fun uu____8672  ->
                                                 let uu____8673 =
                                                   bind rewriter
                                                     (fun uu____8687  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8693  ->
                                                             let uu____8694 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8695 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8694
                                                               uu____8695);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8673)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8736 =
        bind get
          (fun ps  ->
             let uu____8746 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8746 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8783  ->
                       let uu____8784 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8784);
                  bind dismiss_all
                    (fun uu____8787  ->
                       let uu____8788 =
                         let uu____8795 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8795
                           keepGoing gt1
                          in
                       bind uu____8788
                         (fun uu____8807  ->
                            match uu____8807 with
                            | (gt',uu____8815) ->
                                (log ps
                                   (fun uu____8819  ->
                                      let uu____8820 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8820);
                                 (let uu____8821 = push_goals gs  in
                                  bind uu____8821
                                    (fun uu____8826  ->
                                       let uu____8827 =
                                         let uu____8830 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8830]  in
                                       add_goals uu____8827)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8736
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8853 =
        bind get
          (fun ps  ->
             let uu____8863 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8863 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8900  ->
                       let uu____8901 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8901);
                  bind dismiss_all
                    (fun uu____8904  ->
                       let uu____8905 =
                         let uu____8908 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8908 gt1
                          in
                       bind uu____8905
                         (fun gt'  ->
                            log ps
                              (fun uu____8916  ->
                                 let uu____8917 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8917);
                            (let uu____8918 = push_goals gs  in
                             bind uu____8918
                               (fun uu____8923  ->
                                  let uu____8924 =
                                    let uu____8927 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8927]  in
                                  add_goals uu____8924))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8853
  
let (trefl : unit -> unit tac) =
  fun uu____8938  ->
    let uu____8941 =
      let uu____8944 = cur_goal ()  in
      bind uu____8944
        (fun g  ->
           let uu____8962 =
             let uu____8967 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8967  in
           match uu____8962 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8975 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8975 with
                | (hd1,args) ->
                    let uu____9014 =
                      let uu____9027 =
                        let uu____9028 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9028.FStar_Syntax_Syntax.n  in
                      (uu____9027, args)  in
                    (match uu____9014 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9042::(l,uu____9044)::(r,uu____9046)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9093 =
                           let uu____9096 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9096 l r  in
                         bind uu____9093
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____9103 =
                                  let uu____9104 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____9104 l  in
                                let uu____9105 =
                                  let uu____9106 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____9106 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____9103 uu____9105
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____9109) ->
                         let uu____9126 =
                           let uu____9127 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9127 t  in
                         fail1 "trefl: not an equality (%s)" uu____9126))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8941
  
let (dup : unit -> unit tac) =
  fun uu____9140  ->
    let uu____9143 = cur_goal ()  in
    bind uu____9143
      (fun g  ->
         let uu____9149 =
           let uu____9156 = FStar_Tactics_Types.goal_env g  in
           let uu____9157 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9156 uu____9157  in
         bind uu____9149
           (fun uu____9166  ->
              match uu____9166 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___397_9176 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___397_9176.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___397_9176.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___397_9176.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9179  ->
                       let uu____9180 =
                         let uu____9183 = FStar_Tactics_Types.goal_env g  in
                         let uu____9184 =
                           let uu____9185 =
                             let uu____9186 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9187 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9186
                               uu____9187
                              in
                           let uu____9188 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9189 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9185 uu____9188 u
                             uu____9189
                            in
                         add_irrelevant_goal "dup equation" uu____9183
                           uu____9184 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9180
                         (fun uu____9192  ->
                            let uu____9193 = add_goals [g']  in
                            bind uu____9193 (fun uu____9197  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9204  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___398_9221 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___398_9221.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___398_9221.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___398_9221.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___398_9221.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___398_9221.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___398_9221.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___398_9221.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___398_9221.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___398_9221.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___398_9221.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___398_9221.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9222 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9231  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___399_9244 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___399_9244.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___399_9244.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___399_9244.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___399_9244.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___399_9244.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___399_9244.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___399_9244.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___399_9244.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___399_9244.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___399_9244.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___399_9244.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9251  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9258 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9278 =
      let uu____9285 = cur_goal ()  in
      bind uu____9285
        (fun g  ->
           let uu____9295 =
             let uu____9304 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9304 t  in
           bind uu____9295
             (fun uu____9332  ->
                match uu____9332 with
                | (t1,typ,guard) ->
                    let uu____9348 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9348 with
                     | (hd1,args) ->
                         let uu____9397 =
                           let uu____9412 =
                             let uu____9413 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9413.FStar_Syntax_Syntax.n  in
                           (uu____9412, args)  in
                         (match uu____9397 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9434)::(q,uu____9436)::[]) when
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
                                let uu____9490 =
                                  let uu____9491 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9491
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9490
                                 in
                              let g2 =
                                let uu____9493 =
                                  let uu____9494 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9494
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9493
                                 in
                              bind __dismiss
                                (fun uu____9501  ->
                                   let uu____9502 = add_goals [g1; g2]  in
                                   bind uu____9502
                                     (fun uu____9511  ->
                                        let uu____9512 =
                                          let uu____9517 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9518 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9517, uu____9518)  in
                                        ret uu____9512))
                          | uu____9523 ->
                              let uu____9538 =
                                let uu____9539 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9539 typ  in
                              fail1 "Not a disjunction: %s" uu____9538))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9278
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9569 =
      let uu____9572 = cur_goal ()  in
      bind uu____9572
        (fun g  ->
           FStar_Options.push ();
           (let uu____9585 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9585);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___400_9592 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___400_9592.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___400_9592.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___400_9592.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9569
  
let (top_env : unit -> env tac) =
  fun uu____9604  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9617  ->
    let uu____9620 = cur_goal ()  in
    bind uu____9620
      (fun g  ->
         let uu____9626 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9626)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9635  ->
    let uu____9638 = cur_goal ()  in
    bind uu____9638
      (fun g  ->
         let uu____9644 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9644)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9653  ->
    let uu____9656 = cur_goal ()  in
    bind uu____9656
      (fun g  ->
         let uu____9662 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9662)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9679 =
        mlog
          (fun uu____9684  ->
             let uu____9685 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9685)
          (fun uu____9688  ->
             let uu____9689 = cur_goal ()  in
             bind uu____9689
               (fun goal  ->
                  let env =
                    let uu____9697 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9697 ty  in
                  let uu____9698 = __tc env tm  in
                  bind uu____9698
                    (fun uu____9717  ->
                       match uu____9717 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9731  ->
                                let uu____9732 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9732)
                             (fun uu____9734  ->
                                mlog
                                  (fun uu____9737  ->
                                     let uu____9738 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9738)
                                  (fun uu____9741  ->
                                     let uu____9742 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9742
                                       (fun uu____9746  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9679
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9769 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9775 =
              let uu____9782 =
                let uu____9783 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9783
                 in
              new_uvar "uvar_env.2" env uu____9782  in
            bind uu____9775
              (fun uu____9799  ->
                 match uu____9799 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9769
        (fun typ  ->
           let uu____9811 = new_uvar "uvar_env" env typ  in
           bind uu____9811
             (fun uu____9825  -> match uu____9825 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9843 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9862 -> g.FStar_Tactics_Types.opts
             | uu____9865 -> FStar_Options.peek ()  in
           let uu____9868 = FStar_Syntax_Util.head_and_args t  in
           match uu____9868 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9888);
                FStar_Syntax_Syntax.pos = uu____9889;
                FStar_Syntax_Syntax.vars = uu____9890;_},uu____9891)
               ->
               let env1 =
                 let uu___401_9933 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___401_9933.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___401_9933.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___401_9933.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___401_9933.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___401_9933.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___401_9933.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___401_9933.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___401_9933.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___401_9933.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___401_9933.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___401_9933.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___401_9933.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___401_9933.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___401_9933.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___401_9933.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___401_9933.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___401_9933.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___401_9933.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___401_9933.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___401_9933.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___401_9933.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___401_9933.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___401_9933.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___401_9933.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___401_9933.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___401_9933.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___401_9933.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___401_9933.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___401_9933.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___401_9933.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___401_9933.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___401_9933.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___401_9933.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___401_9933.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___401_9933.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___401_9933.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___401_9933.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___401_9933.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___401_9933.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___401_9933.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9935 =
                 let uu____9938 = bnorm_goal g  in [uu____9938]  in
               add_goals uu____9935
           | uu____9939 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9843
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9988 = if b then t2 else ret false  in
             bind uu____9988 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9999 = trytac comp  in
      bind uu____9999
        (fun uu___343_10007  ->
           match uu___343_10007 with
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
        let uu____10033 =
          bind get
            (fun ps  ->
               let uu____10039 = __tc e t1  in
               bind uu____10039
                 (fun uu____10059  ->
                    match uu____10059 with
                    | (t11,ty1,g1) ->
                        let uu____10071 = __tc e t2  in
                        bind uu____10071
                          (fun uu____10091  ->
                             match uu____10091 with
                             | (t21,ty2,g2) ->
                                 let uu____10103 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10103
                                   (fun uu____10108  ->
                                      let uu____10109 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10109
                                        (fun uu____10115  ->
                                           let uu____10116 =
                                             do_unify e ty1 ty2  in
                                           let uu____10119 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10116 uu____10119)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10033
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10152  ->
             let uu____10153 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10153
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
        (fun uu____10174  ->
           let uu____10175 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10175)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10185 =
      mlog
        (fun uu____10190  ->
           let uu____10191 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10191)
        (fun uu____10194  ->
           let uu____10195 = cur_goal ()  in
           bind uu____10195
             (fun g  ->
                let uu____10201 =
                  let uu____10210 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10210 ty  in
                bind uu____10201
                  (fun uu____10222  ->
                     match uu____10222 with
                     | (ty1,uu____10232,guard) ->
                         let uu____10234 =
                           let uu____10237 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10237 guard  in
                         bind uu____10234
                           (fun uu____10240  ->
                              let uu____10241 =
                                let uu____10244 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10245 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10244 uu____10245 ty1  in
                              bind uu____10241
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10251 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10251
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Normalize.Reify;
                                        FStar_TypeChecker_Normalize.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                        FStar_TypeChecker_Normalize.Primops;
                                        FStar_TypeChecker_Normalize.Simplify;
                                        FStar_TypeChecker_Normalize.UnfoldTac;
                                        FStar_TypeChecker_Normalize.Unmeta]
                                         in
                                      let ng =
                                        let uu____10257 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10258 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10257
                                          uu____10258
                                         in
                                      let nty =
                                        let uu____10260 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10260 ty1  in
                                      let uu____10261 =
                                        let uu____10264 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10264 ng nty  in
                                      bind uu____10261
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10270 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10270
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10185
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10292::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10320 = init xs  in x :: uu____10320
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____10332 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____10340) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10405 = last args  in
          (match uu____10405 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10435 =
                 let uu____10436 =
                   let uu____10441 =
                     let uu____10442 =
                       let uu____10447 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10447  in
                     uu____10442 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10441, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10436  in
               FStar_All.pipe_left ret uu____10435)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10460,uu____10461) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10513 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10513 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10554 =
                      let uu____10555 =
                        let uu____10560 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10560)  in
                      FStar_Reflection_Data.Tv_Abs uu____10555  in
                    FStar_All.pipe_left ret uu____10554))
      | FStar_Syntax_Syntax.Tm_type uu____10563 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10587 ->
          let uu____10602 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10602 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10632 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10632 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10685 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10697 =
            let uu____10698 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10698  in
          FStar_All.pipe_left ret uu____10697
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10719 =
            let uu____10720 =
              let uu____10725 =
                let uu____10726 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10726  in
              (uu____10725, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10720  in
          FStar_All.pipe_left ret uu____10719
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10760 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10765 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10765 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10818 ->
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
             | FStar_Util.Inr uu____10852 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10856 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10856 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10876 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10880 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10934 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10934
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10953 =
                  let uu____10960 =
                    FStar_List.map
                      (fun uu____10972  ->
                         match uu____10972 with
                         | (p1,uu____10980) -> inspect_pat p1) ps
                     in
                  (fv, uu____10960)  in
                FStar_Reflection_Data.Pat_Cons uu____10953
            | FStar_Syntax_Syntax.Pat_var bv ->
                FStar_Reflection_Data.Pat_Var bv
            | FStar_Syntax_Syntax.Pat_wild bv ->
                FStar_Reflection_Data.Pat_Wild bv
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___344_11074  ->
                 match uu___344_11074 with
                 | (pat,uu____11096,t4) ->
                     let uu____11114 = inspect_pat pat  in (uu____11114, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____11123 ->
          ((let uu____11125 =
              let uu____11130 =
                let uu____11131 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____11132 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____11131 uu____11132
                 in
              (FStar_Errors.Warning_CantInspect, uu____11130)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____11125);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____10332
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____11145 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____11145
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____11149 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____11149
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____11153 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____11153
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____11160 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____11160
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____11185 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____11185
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____11202 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____11202
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____11221 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____11221
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11225 =
          let uu____11226 =
            let uu____11233 =
              let uu____11234 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____11234  in
            FStar_Syntax_Syntax.mk uu____11233  in
          uu____11226 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____11225
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____11242 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11242
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____11251 =
          let uu____11252 =
            let uu____11259 =
              let uu____11260 =
                let uu____11273 =
                  let uu____11276 =
                    let uu____11277 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____11277]  in
                  FStar_Syntax_Subst.close uu____11276 t2  in
                ((false, [lb]), uu____11273)  in
              FStar_Syntax_Syntax.Tm_let uu____11260  in
            FStar_Syntax_Syntax.mk uu____11259  in
          uu____11252 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____11251
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____11317 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____11317 with
         | (lbs,body) ->
             let uu____11332 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____11332)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11366 =
                let uu____11367 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____11367  in
              FStar_All.pipe_left wrap uu____11366
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____11374 =
                let uu____11375 =
                  let uu____11388 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____11404 = pack_pat p1  in
                         (uu____11404, false)) ps
                     in
                  (fv, uu____11388)  in
                FStar_Syntax_Syntax.Pat_cons uu____11375  in
              FStar_All.pipe_left wrap uu____11374
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
            (fun uu___345_11450  ->
               match uu___345_11450 with
               | (pat,t1) ->
                   let uu____11467 = pack_pat pat  in
                   (uu____11467, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11515 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11515
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11543 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11543
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11589 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11589
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11628 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11628
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11649 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11649 with
      | (u,ctx_uvars,g_u) ->
          let uu____11681 = FStar_List.hd ctx_uvars  in
          (match uu____11681 with
           | (ctx_uvar,uu____11695) ->
               let g =
                 let uu____11697 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11697 false
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
        let uu____11717 = goal_of_goal_ty env typ  in
        match uu____11717 with
        | (g,g_u) ->
            let ps =
              let uu____11729 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
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
                FStar_Tactics_Types.psc =
                  FStar_TypeChecker_Normalize.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____11729
              }  in
            let uu____11734 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11734)
  