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
                 let uu___351_1033 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___351_1033.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___351_1033.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___351_1033.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___351_1033.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___351_1033.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___351_1033.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___351_1033.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___351_1033.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___351_1033.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___351_1033.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___351_1033.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___356_1309 = ps  in
         let uu____1310 =
           FStar_List.filter
             (fun g  ->
                let uu____1316 = check_goal_solved g  in
                FStar_Option.isNone uu____1316) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___356_1309.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___356_1309.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___356_1309.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1310;
           FStar_Tactics_Types.smt_goals =
             (uu___356_1309.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___356_1309.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___356_1309.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___356_1309.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___356_1309.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___356_1309.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___356_1309.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___356_1309.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___357_1364 = p  in
         let uu____1365 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___357_1364.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___357_1364.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___357_1364.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1365;
           FStar_Tactics_Types.smt_goals =
             (uu___357_1364.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___357_1364.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___357_1364.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___357_1364.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___357_1364.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___357_1364.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___357_1364.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___357_1364.FStar_Tactics_Types.tac_verb_dbg)
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
         (let uu___358_1455 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___358_1455.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___358_1455.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___358_1455.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___358_1455.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___358_1455.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___358_1455.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___358_1455.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___358_1455.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___358_1455.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___358_1455.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___358_1455.FStar_Tactics_Types.tac_verb_dbg)
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
         ((let uu____1542 =
             let uu____1543 = FStar_Tactics_Types.goal_type g  in
             uu____1543.FStar_Syntax_Syntax.pos  in
           let uu____1546 =
             let uu____1551 =
               let uu____1552 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1552
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1551)  in
           FStar_Errors.log_issue uu____1542 uu____1546);
          (let uu____1553 =
             let uu____1554 = FStar_ST.op_Bang nwarn  in
             uu____1554 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1553))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___359_1622 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1622.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1622.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_1622.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___359_1622.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1622.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1622.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1622.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1622.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1622.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1622.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1622.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___360_1642 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1642.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1642.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___360_1642.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1642.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1642.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1642.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1642.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1642.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1642.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1642.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1642.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___361_1662 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___361_1662.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___361_1662.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___361_1662.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___361_1662.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___361_1662.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___361_1662.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___361_1662.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___361_1662.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___361_1662.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___361_1662.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___361_1662.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___362_1682 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_1682.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_1682.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___362_1682.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___362_1682.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___362_1682.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_1682.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_1682.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_1682.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_1682.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_1682.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_1682.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1693  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___363_1707 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_1707.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_1707.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___363_1707.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___363_1707.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_1707.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_1707.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_1707.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_1707.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___363_1707.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___363_1707.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_1707.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1735 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1735 with
        | (u,ctx_uvar,g_u) ->
            let uu____1769 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1769
              (fun uu____1778  ->
                 let uu____1779 =
                   let uu____1784 =
                     let uu____1785 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1785  in
                   (u, uu____1784)  in
                 ret uu____1779)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1803 = FStar_Syntax_Util.un_squash t  in
    match uu____1803 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1813 =
          let uu____1814 = FStar_Syntax_Subst.compress t'  in
          uu____1814.FStar_Syntax_Syntax.n  in
        (match uu____1813 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1818 -> false)
    | uu____1819 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1829 = FStar_Syntax_Util.un_squash t  in
    match uu____1829 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1839 =
          let uu____1840 = FStar_Syntax_Subst.compress t'  in
          uu____1840.FStar_Syntax_Syntax.n  in
        (match uu____1839 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1844 -> false)
    | uu____1845 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1856  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1867 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1867 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1874 = goal_to_string_verbose hd1  in
                    let uu____1875 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1874 uu____1875);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1882  ->
    let uu____1885 =
      bind get
        (fun ps  ->
           let uu____1891 = cur_goal ()  in
           bind uu____1891
             (fun g  ->
                (let uu____1898 =
                   let uu____1899 = FStar_Tactics_Types.goal_type g  in
                   uu____1899.FStar_Syntax_Syntax.pos  in
                 let uu____1902 =
                   let uu____1907 =
                     let uu____1908 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1908
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1907)  in
                 FStar_Errors.log_issue uu____1898 uu____1902);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1885
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1919  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___364_1929 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___364_1929.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___364_1929.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___364_1929.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___364_1929.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___364_1929.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___364_1929.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___364_1929.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___364_1929.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___364_1929.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___364_1929.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___364_1929.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1930 = set ps1  in
         bind uu____1930
           (fun uu____1935  ->
              let uu____1936 = FStar_BigInt.of_int_fs n1  in ret uu____1936))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1943  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1951 = FStar_BigInt.of_int_fs n1  in ret uu____1951)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1964  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1972 = FStar_BigInt.of_int_fs n1  in ret uu____1972)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1985  ->
    let uu____1988 = cur_goal ()  in
    bind uu____1988 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2020 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2020 phi  in
          let uu____2021 = new_uvar reason env typ  in
          bind uu____2021
            (fun uu____2036  ->
               match uu____2036 with
               | (uu____2043,ctx_uvar) ->
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
             (fun uu____2088  ->
                let uu____2089 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2089)
             (fun uu____2092  ->
                let e1 =
                  let uu___365_2094 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___365_2094.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___365_2094.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___365_2094.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___365_2094.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___365_2094.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___365_2094.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___365_2094.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___365_2094.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___365_2094.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___365_2094.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___365_2094.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___365_2094.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___365_2094.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___365_2094.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___365_2094.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___365_2094.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___365_2094.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___365_2094.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___365_2094.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___365_2094.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___365_2094.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___365_2094.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___365_2094.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___365_2094.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___365_2094.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___365_2094.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___365_2094.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___365_2094.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___365_2094.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___365_2094.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___365_2094.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___365_2094.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___365_2094.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___365_2094.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___365_2094.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___365_2094.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___365_2094.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___365_2094.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___365_2094.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___365_2094.FStar_TypeChecker_Env.dep_graph)
                  }  in
                try
                  let uu____2114 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2114
                with
                | FStar_Errors.Err (uu____2141,msg) ->
                    let uu____2143 = tts e1 t  in
                    let uu____2144 =
                      let uu____2145 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2145
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2143 uu____2144 msg
                | FStar_Errors.Error (uu____2152,msg,uu____2154) ->
                    let uu____2155 = tts e1 t  in
                    let uu____2156 =
                      let uu____2157 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2157
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2155 uu____2156 msg))
  
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
  fun uu____2184  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___368_2202 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_2202.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_2202.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_2202.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___368_2202.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___368_2202.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_2202.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_2202.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_2202.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_2202.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___368_2202.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_2202.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2226 = get_guard_policy ()  in
      bind uu____2226
        (fun old_pol  ->
           let uu____2232 = set_guard_policy pol  in
           bind uu____2232
             (fun uu____2236  ->
                bind t
                  (fun r  ->
                     let uu____2240 = set_guard_policy old_pol  in
                     bind uu____2240 (fun uu____2244  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2247 = let uu____2252 = cur_goal ()  in trytac uu____2252  in
  bind uu____2247
    (fun uu___341_2259  ->
       match uu___341_2259 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2265 = FStar_Options.peek ()  in ret uu____2265)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2288 =
               let uu____2289 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2289.FStar_TypeChecker_Env.guard_f  in
             match uu____2288 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2293 = istrivial e f  in
                 if uu____2293
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2301 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2301
                              (fun goal  ->
                                 let goal1 =
                                   let uu___369_2308 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___369_2308.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___369_2308.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___369_2308.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2309 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2309
                              (fun goal  ->
                                 let goal1 =
                                   let uu___370_2316 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___370_2316.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___370_2316.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___370_2316.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2324 =
                                 let uu____2325 =
                                   let uu____2326 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2326
                                    in
                                 Prims.op_Negation uu____2325  in
                               if uu____2324
                               then
                                 mlog
                                   (fun uu____2331  ->
                                      let uu____2332 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2332)
                                   (fun uu____2334  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2341 ->
                                 mlog
                                   (fun uu____2344  ->
                                      let uu____2345 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2345)
                                   (fun uu____2347  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2357 =
      let uu____2360 = cur_goal ()  in
      bind uu____2360
        (fun goal  ->
           let uu____2366 =
             let uu____2375 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2375 t  in
           bind uu____2366
             (fun uu____2387  ->
                match uu____2387 with
                | (t1,typ,guard) ->
                    let uu____2399 =
                      let uu____2402 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2402 guard  in
                    bind uu____2399 (fun uu____2404  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2357
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2433 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2433 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2444  ->
    let uu____2447 = cur_goal ()  in
    bind uu____2447
      (fun goal  ->
         let uu____2453 =
           let uu____2454 = FStar_Tactics_Types.goal_env goal  in
           let uu____2455 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2454 uu____2455  in
         if uu____2453
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2459 =
              let uu____2460 = FStar_Tactics_Types.goal_env goal  in
              let uu____2461 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2460 uu____2461  in
            fail1 "Not a trivial goal: %s" uu____2459))
  
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
          let uu____2490 =
            let uu____2491 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2491.FStar_TypeChecker_Env.guard_f  in
          match uu____2490 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2499 = istrivial e f  in
              if uu____2499
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2507 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2507
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___373_2517 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___373_2517.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___373_2517.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___373_2517.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2524  ->
    let uu____2527 = cur_goal ()  in
    bind uu____2527
      (fun g  ->
         let uu____2533 = is_irrelevant g  in
         if uu____2533
         then bind __dismiss (fun uu____2537  -> add_smt_goals [g])
         else
           (let uu____2539 =
              let uu____2540 = FStar_Tactics_Types.goal_env g  in
              let uu____2541 = FStar_Tactics_Types.goal_type g  in
              tts uu____2540 uu____2541  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2539))
  
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
             let uu____2590 =
               try
                 let uu____2624 =
                   let uu____2633 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2633 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2624
               with | uu____2655 -> fail "divide: not enough goals"  in
             bind uu____2590
               (fun uu____2681  ->
                  match uu____2681 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___374_2707 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___374_2707.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___374_2707.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___374_2707.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___374_2707.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___374_2707.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___374_2707.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___374_2707.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___374_2707.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___374_2707.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___374_2707.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2708 = set lp  in
                      bind uu____2708
                        (fun uu____2716  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___375_2732 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___375_2732.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___375_2732.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___375_2732.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___375_2732.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___375_2732.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___375_2732.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___375_2732.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___375_2732.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___375_2732.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___375_2732.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2733 = set rp  in
                                     bind uu____2733
                                       (fun uu____2741  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___376_2757 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___376_2757.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___376_2757.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2758 = set p'
                                                       in
                                                    bind uu____2758
                                                      (fun uu____2766  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2772 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2793 = divide FStar_BigInt.one f idtac  in
    bind uu____2793
      (fun uu____2806  -> match uu____2806 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2843::uu____2844 ->
             let uu____2847 =
               let uu____2856 = map tau  in
               divide FStar_BigInt.one tau uu____2856  in
             bind uu____2847
               (fun uu____2874  ->
                  match uu____2874 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2915 =
        bind t1
          (fun uu____2920  ->
             let uu____2921 = map t2  in
             bind uu____2921 (fun uu____2929  -> ret ()))
         in
      focus uu____2915
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2938  ->
    let uu____2941 =
      let uu____2944 = cur_goal ()  in
      bind uu____2944
        (fun goal  ->
           let uu____2953 =
             let uu____2960 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2960  in
           match uu____2953 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2969 =
                 let uu____2970 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2970  in
               if uu____2969
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2975 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2975 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2989 = new_uvar "intro" env' typ'  in
                  bind uu____2989
                    (fun uu____3005  ->
                       match uu____3005 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3029 = set_solution goal sol  in
                           bind uu____3029
                             (fun uu____3035  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3037 =
                                  let uu____3040 = bnorm_goal g  in
                                  replace_cur uu____3040  in
                                bind uu____3037 (fun uu____3042  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3047 =
                 let uu____3048 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3049 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3048 uu____3049  in
               fail1 "goal is not an arrow (%s)" uu____3047)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2941
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3064  ->
    let uu____3071 = cur_goal ()  in
    bind uu____3071
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3088 =
            let uu____3095 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3095  in
          match uu____3088 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3108 =
                let uu____3109 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3109  in
              if uu____3108
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3122 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3122
                    in
                 let bs =
                   let uu____3132 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3132; b]  in
                 let env' =
                   let uu____3158 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3158 bs  in
                 let uu____3159 =
                   let uu____3166 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3166  in
                 bind uu____3159
                   (fun uu____3185  ->
                      match uu____3185 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3199 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3202 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3199
                              FStar_Parser_Const.effect_Tot_lid uu____3202 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3220 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3220 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3242 =
                                   let uu____3243 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3243.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3242
                                  in
                               let uu____3256 = set_solution goal tm  in
                               bind uu____3256
                                 (fun uu____3265  ->
                                    let uu____3266 =
                                      let uu____3269 =
                                        bnorm_goal
                                          (let uu___379_3272 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___379_3272.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___379_3272.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___379_3272.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3269  in
                                    bind uu____3266
                                      (fun uu____3279  ->
                                         let uu____3280 =
                                           let uu____3285 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3285, b)  in
                                         ret uu____3280)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3294 =
                let uu____3295 = FStar_Tactics_Types.goal_env goal  in
                let uu____3296 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3295 uu____3296  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3294))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3314 = cur_goal ()  in
    bind uu____3314
      (fun goal  ->
         mlog
           (fun uu____3321  ->
              let uu____3322 =
                let uu____3323 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3323  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3322)
           (fun uu____3328  ->
              let steps =
                let uu____3332 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3332
                 in
              let t =
                let uu____3336 = FStar_Tactics_Types.goal_env goal  in
                let uu____3337 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3336 uu____3337  in
              let uu____3338 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3338))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3362 =
          mlog
            (fun uu____3367  ->
               let uu____3368 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3368)
            (fun uu____3370  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3376 -> g.FStar_Tactics_Types.opts
                      | uu____3379 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3384  ->
                         let uu____3385 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3385)
                      (fun uu____3388  ->
                         let uu____3389 = __tc e t  in
                         bind uu____3389
                           (fun uu____3410  ->
                              match uu____3410 with
                              | (t1,uu____3420,uu____3421) ->
                                  let steps =
                                    let uu____3425 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3425
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3362
  
let (refine_intro : unit -> unit tac) =
  fun uu____3439  ->
    let uu____3442 =
      let uu____3445 = cur_goal ()  in
      bind uu____3445
        (fun g  ->
           let uu____3452 =
             let uu____3463 = FStar_Tactics_Types.goal_env g  in
             let uu____3464 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3463 uu____3464
              in
           match uu____3452 with
           | (uu____3467,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3492 =
                 let uu____3497 =
                   let uu____3502 =
                     let uu____3503 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3503]  in
                   FStar_Syntax_Subst.open_term uu____3502 phi  in
                 match uu____3497 with
                 | (bvs,phi1) ->
                     let uu____3528 =
                       let uu____3529 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3529  in
                     (uu____3528, phi1)
                  in
               (match uu____3492 with
                | (bv1,phi1) ->
                    let uu____3548 =
                      let uu____3551 = FStar_Tactics_Types.goal_env g  in
                      let uu____3552 =
                        let uu____3553 =
                          let uu____3556 =
                            let uu____3557 =
                              let uu____3564 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3564)  in
                            FStar_Syntax_Syntax.NT uu____3557  in
                          [uu____3556]  in
                        FStar_Syntax_Subst.subst uu____3553 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3551
                        uu____3552 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3548
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3572  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3442
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3591 = cur_goal ()  in
      bind uu____3591
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3599 = FStar_Tactics_Types.goal_env goal  in
               let uu____3600 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3599 uu____3600
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3602 = __tc env t  in
           bind uu____3602
             (fun uu____3621  ->
                match uu____3621 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3636  ->
                         let uu____3637 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3638 =
                           let uu____3639 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3639
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3637 uu____3638)
                      (fun uu____3642  ->
                         let uu____3643 =
                           let uu____3646 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3646 guard  in
                         bind uu____3643
                           (fun uu____3648  ->
                              mlog
                                (fun uu____3652  ->
                                   let uu____3653 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3654 =
                                     let uu____3655 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3655
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3653 uu____3654)
                                (fun uu____3658  ->
                                   let uu____3659 =
                                     let uu____3662 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3663 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3662 typ uu____3663  in
                                   bind uu____3659
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3669 =
                                             let uu____3670 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3670 t1  in
                                           let uu____3671 =
                                             let uu____3672 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3672 typ  in
                                           let uu____3673 =
                                             let uu____3674 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3675 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3674 uu____3675  in
                                           let uu____3676 =
                                             let uu____3677 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3678 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3677 uu____3678  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3669 uu____3671 uu____3673
                                             uu____3676)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3693 =
        mlog
          (fun uu____3698  ->
             let uu____3699 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3699)
          (fun uu____3702  ->
             let uu____3703 =
               let uu____3710 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3710  in
             bind uu____3703
               (fun uu___343_3719  ->
                  match uu___343_3719 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3729  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3732  ->
                           let uu____3733 =
                             let uu____3740 =
                               let uu____3743 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3743
                                 (fun uu____3748  ->
                                    let uu____3749 = refine_intro ()  in
                                    bind uu____3749
                                      (fun uu____3753  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3740  in
                           bind uu____3733
                             (fun uu___342_3760  ->
                                match uu___342_3760 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3768 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3693
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3818 = f x  in
          bind uu____3818
            (fun y  ->
               let uu____3826 = mapM f xs  in
               bind uu____3826 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3897 = do_unify e ty1 ty2  in
          bind uu____3897
            (fun uu___344_3909  ->
               if uu___344_3909
               then ret acc
               else
                 (let uu____3928 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3928 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3949 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3950 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3949
                        uu____3950
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3965 =
                        let uu____3966 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3966  in
                      if uu____3965
                      then fail "Codomain is effectful"
                      else
                        (let uu____3986 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3986
                           (fun uu____4012  ->
                              match uu____4012 with
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
      let uu____4098 =
        mlog
          (fun uu____4103  ->
             let uu____4104 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4104)
          (fun uu____4107  ->
             let uu____4108 = cur_goal ()  in
             bind uu____4108
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4116 = __tc e tm  in
                  bind uu____4116
                    (fun uu____4137  ->
                       match uu____4137 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4150 =
                             let uu____4161 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4161  in
                           bind uu____4150
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4204  ->
                                       fun w  ->
                                         match uu____4204 with
                                         | (uvt,q,uu____4222) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4254 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4271  ->
                                       fun s  ->
                                         match uu____4271 with
                                         | (uu____4283,uu____4284,uv) ->
                                             let uu____4286 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4286) uvs uu____4254
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4295 = solve' goal w  in
                                bind uu____4295
                                  (fun uu____4300  ->
                                     let uu____4301 =
                                       mapM
                                         (fun uu____4318  ->
                                            match uu____4318 with
                                            | (uvt,q,uv) ->
                                                let uu____4330 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4330 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4335 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4336 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4336
                                                     then ret ()
                                                     else
                                                       (let uu____4340 =
                                                          let uu____4343 =
                                                            bnorm_goal
                                                              (let uu___380_4346
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___380_4346.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___380_4346.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4343]  in
                                                        add_goals uu____4340)))
                                         uvs
                                        in
                                     bind uu____4301
                                       (fun uu____4350  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4098
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4375 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4375
    then
      let uu____4382 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4397 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4450 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4382 with
      | (pre,post) ->
          let post1 =
            let uu____4482 =
              let uu____4493 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4493]  in
            FStar_Syntax_Util.mk_app post uu____4482  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4523 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4523
       then
         let uu____4530 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4530
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4563 =
      let uu____4566 =
        mlog
          (fun uu____4571  ->
             let uu____4572 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4572)
          (fun uu____4576  ->
             let is_unit_t t =
               let uu____4583 =
                 let uu____4584 = FStar_Syntax_Subst.compress t  in
                 uu____4584.FStar_Syntax_Syntax.n  in
               match uu____4583 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4588 -> false  in
             let uu____4589 = cur_goal ()  in
             bind uu____4589
               (fun goal  ->
                  let uu____4595 =
                    let uu____4604 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4604 tm  in
                  bind uu____4595
                    (fun uu____4619  ->
                       match uu____4619 with
                       | (tm1,t,guard) ->
                           let uu____4631 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4631 with
                            | (bs,comp) ->
                                let uu____4664 = lemma_or_sq comp  in
                                (match uu____4664 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4683 =
                                       FStar_List.fold_left
                                         (fun uu____4731  ->
                                            fun uu____4732  ->
                                              match (uu____4731, uu____4732)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4845 =
                                                    is_unit_t b_t  in
                                                  if uu____4845
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4883 =
                                                       let uu____4896 =
                                                         let uu____4897 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4897.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4900 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4896
                                                         uu____4900 b_t
                                                        in
                                                     match uu____4883 with
                                                     | (u,uu____4918,g_u) ->
                                                         let uu____4932 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4932,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4683 with
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
                                          let uu____5011 =
                                            let uu____5014 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____5015 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____5016 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____5014 uu____5015
                                              uu____5016
                                             in
                                          bind uu____5011
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____5024 =
                                                   let uu____5025 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____5025 tm1  in
                                                 let uu____5026 =
                                                   let uu____5027 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5028 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____5027 uu____5028
                                                    in
                                                 let uu____5029 =
                                                   let uu____5030 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5031 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____5030 uu____5031
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____5024 uu____5026
                                                   uu____5029
                                               else
                                                 (let uu____5033 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____5033
                                                    (fun uu____5038  ->
                                                       let uu____5039 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____5039
                                                         (fun uu____5047  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____5072
                                                                  =
                                                                  let uu____5075
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____5075
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____5072
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
                                                                   let uu____5110
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5110)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5126
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5126
                                                              with
                                                              | (hd1,uu____5144)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5170)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5187
                                                                    -> false)
                                                               in
                                                            let uu____5188 =
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
                                                                    let uu____5236
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5236
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5264)
                                                                    ->
                                                                    let uu____5289
                                                                    =
                                                                    let uu____5290
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5290.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5289
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5304)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___381_5324
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___381_5324.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___381_5324.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___381_5324.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5337
                                                                    ->
                                                                    let env =
                                                                    let uu___382_5339
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___382_5339.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5341
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5341
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
                                                                    let uu____5344
                                                                    =
                                                                    let uu____5351
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5351
                                                                    term1  in
                                                                    match uu____5344
                                                                    with
                                                                    | 
                                                                    (uu____5352,uu____5353,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5355
                                                                    =
                                                                    let uu____5360
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5360
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5355
                                                                    (fun
                                                                    uu___345_5372
                                                                     ->
                                                                    match uu___345_5372
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
                                                            bind uu____5188
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5440
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5440
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5462
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5462
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5523
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5523
                                                                    then
                                                                    let uu____5526
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5526
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
                                                                    let uu____5540
                                                                    =
                                                                    let uu____5541
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5541
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5540)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5542
                                                                   =
                                                                   let uu____5545
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5545
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5542
                                                                   (fun
                                                                    uu____5548
                                                                     ->
                                                                    let uu____5549
                                                                    =
                                                                    let uu____5552
                                                                    =
                                                                    let uu____5553
                                                                    =
                                                                    let uu____5554
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5555
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5554
                                                                    uu____5555
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5553
                                                                     in
                                                                    if
                                                                    uu____5552
                                                                    then
                                                                    let uu____5558
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5558
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5549
                                                                    (fun
                                                                    uu____5562
                                                                     ->
                                                                    let uu____5563
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5563
                                                                    (fun
                                                                    uu____5567
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4566  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4563
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5589 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5589 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5599::(e1,uu____5601)::(e2,uu____5603)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5664 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5688 = destruct_eq' typ  in
    match uu____5688 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5718 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5718 with
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
        let uu____5780 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5780 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5828 = aux e'  in
               FStar_Util.map_opt uu____5828
                 (fun uu____5852  ->
                    match uu____5852 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5873 = aux e  in
      FStar_Util.map_opt uu____5873
        (fun uu____5897  ->
           match uu____5897 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5964 =
            let uu____5973 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5973  in
          FStar_Util.map_opt uu____5964
            (fun uu____5988  ->
               match uu____5988 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___383_6007 = bv  in
                     let uu____6008 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___383_6007.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___383_6007.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____6008
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___384_6016 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6017 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6026 =
                       let uu____6029 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6029  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___384_6016.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6017;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6026;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___384_6016.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___384_6016.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___384_6016.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___385_6030 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___385_6030.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___385_6030.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___385_6030.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6040 =
      let uu____6043 = cur_goal ()  in
      bind uu____6043
        (fun goal  ->
           let uu____6051 = h  in
           match uu____6051 with
           | (bv,uu____6055) ->
               mlog
                 (fun uu____6063  ->
                    let uu____6064 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6065 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6064
                      uu____6065)
                 (fun uu____6068  ->
                    let uu____6069 =
                      let uu____6078 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6078  in
                    match uu____6069 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6099 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6099 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6114 =
                               let uu____6115 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6115.FStar_Syntax_Syntax.n  in
                             (match uu____6114 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___386_6132 = bv1  in
                                    let uu____6133 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___386_6132.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___386_6132.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6133
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___387_6141 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6142 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6151 =
                                      let uu____6154 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6154
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___387_6141.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6142;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6151;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___387_6141.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___387_6141.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___387_6141.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___388_6157 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___388_6157.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___388_6157.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___388_6157.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6158 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6159 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6040
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6184 =
        let uu____6187 = cur_goal ()  in
        bind uu____6187
          (fun goal  ->
             let uu____6198 = b  in
             match uu____6198 with
             | (bv,uu____6202) ->
                 let bv' =
                   let uu____6208 =
                     let uu___389_6209 = bv  in
                     let uu____6210 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6210;
                       FStar_Syntax_Syntax.index =
                         (uu___389_6209.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___389_6209.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6208  in
                 let s1 =
                   let uu____6214 =
                     let uu____6215 =
                       let uu____6222 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6222)  in
                     FStar_Syntax_Syntax.NT uu____6215  in
                   [uu____6214]  in
                 let uu____6227 = subst_goal bv bv' s1 goal  in
                 (match uu____6227 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6184
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6246 =
      let uu____6249 = cur_goal ()  in
      bind uu____6249
        (fun goal  ->
           let uu____6258 = b  in
           match uu____6258 with
           | (bv,uu____6262) ->
               let uu____6267 =
                 let uu____6276 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6276  in
               (match uu____6267 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6297 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6297 with
                     | (ty,u) ->
                         let uu____6306 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6306
                           (fun uu____6324  ->
                              match uu____6324 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___390_6334 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___390_6334.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___390_6334.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6338 =
                                      let uu____6339 =
                                        let uu____6346 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6346)  in
                                      FStar_Syntax_Syntax.NT uu____6339  in
                                    [uu____6338]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___391_6358 = b1  in
                                         let uu____6359 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___391_6358.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___391_6358.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6359
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6366  ->
                                       let new_goal =
                                         let uu____6368 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6369 =
                                           let uu____6370 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6370
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6368 uu____6369
                                          in
                                       let uu____6371 = add_goals [new_goal]
                                          in
                                       bind uu____6371
                                         (fun uu____6376  ->
                                            let uu____6377 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6377
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6246
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6400 =
        let uu____6403 = cur_goal ()  in
        bind uu____6403
          (fun goal  ->
             let uu____6412 = b  in
             match uu____6412 with
             | (bv,uu____6416) ->
                 let uu____6421 =
                   let uu____6430 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6430  in
                 (match uu____6421 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6454 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6454
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___392_6459 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___392_6459.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___392_6459.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6461 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6461))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6400
  
let (revert : unit -> unit tac) =
  fun uu____6472  ->
    let uu____6475 = cur_goal ()  in
    bind uu____6475
      (fun goal  ->
         let uu____6481 =
           let uu____6488 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6488  in
         match uu____6481 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6504 =
                 let uu____6507 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6507  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6504
                in
             let uu____6522 = new_uvar "revert" env' typ'  in
             bind uu____6522
               (fun uu____6537  ->
                  match uu____6537 with
                  | (r,u_r) ->
                      let uu____6546 =
                        let uu____6549 =
                          let uu____6550 =
                            let uu____6551 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6551.FStar_Syntax_Syntax.pos  in
                          let uu____6554 =
                            let uu____6559 =
                              let uu____6560 =
                                let uu____6569 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6569  in
                              [uu____6560]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6559  in
                          uu____6554 FStar_Pervasives_Native.None uu____6550
                           in
                        set_solution goal uu____6549  in
                      bind uu____6546
                        (fun uu____6590  ->
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
      let uu____6602 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6602
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6617 = cur_goal ()  in
    bind uu____6617
      (fun goal  ->
         mlog
           (fun uu____6625  ->
              let uu____6626 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6627 =
                let uu____6628 =
                  let uu____6629 =
                    let uu____6638 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6638  in
                  FStar_All.pipe_right uu____6629 FStar_List.length  in
                FStar_All.pipe_right uu____6628 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6626 uu____6627)
           (fun uu____6655  ->
              let uu____6656 =
                let uu____6665 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6665  in
              match uu____6656 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6704 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6704
                        then
                          let uu____6707 =
                            let uu____6708 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6708
                             in
                          fail uu____6707
                        else check1 bvs2
                     in
                  let uu____6710 =
                    let uu____6711 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6711  in
                  if uu____6710
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6715 = check1 bvs  in
                     bind uu____6715
                       (fun uu____6721  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6723 =
                            let uu____6730 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6730  in
                          bind uu____6723
                            (fun uu____6739  ->
                               match uu____6739 with
                               | (ut,uvar_ut) ->
                                   let uu____6748 = set_solution goal ut  in
                                   bind uu____6748
                                     (fun uu____6753  ->
                                        let uu____6754 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6754))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6761  ->
    let uu____6764 = cur_goal ()  in
    bind uu____6764
      (fun goal  ->
         let uu____6770 =
           let uu____6777 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6777  in
         match uu____6770 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6785) ->
             let uu____6790 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6790)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6800 = cur_goal ()  in
    bind uu____6800
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6810 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6810  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6813  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6823 = cur_goal ()  in
    bind uu____6823
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6833 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6833  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6836  -> add_goals [g']))
  
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
            let uu____6876 = FStar_Syntax_Subst.compress t  in
            uu____6876.FStar_Syntax_Syntax.n  in
          let uu____6879 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___396_6885 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___396_6885.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___396_6885.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6879
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6901 =
                   let uu____6902 = FStar_Syntax_Subst.compress t1  in
                   uu____6902.FStar_Syntax_Syntax.n  in
                 match uu____6901 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6933 = ff hd1  in
                     bind uu____6933
                       (fun hd2  ->
                          let fa uu____6959 =
                            match uu____6959 with
                            | (a,q) ->
                                let uu____6980 = ff a  in
                                bind uu____6980 (fun a1  -> ret (a1, q))
                             in
                          let uu____6999 = mapM fa args  in
                          bind uu____6999
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7081 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7081 with
                      | (bs1,t') ->
                          let uu____7090 =
                            let uu____7093 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7093 t'  in
                          bind uu____7090
                            (fun t''  ->
                               let uu____7097 =
                                 let uu____7098 =
                                   let uu____7117 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7126 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7117, uu____7126, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7098  in
                               ret uu____7097))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7201 = ff hd1  in
                     bind uu____7201
                       (fun hd2  ->
                          let ffb br =
                            let uu____7216 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7216 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7248 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7248  in
                                let uu____7249 = ff1 e  in
                                bind uu____7249
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7264 = mapM ffb brs  in
                          bind uu____7264
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7308;
                          FStar_Syntax_Syntax.lbtyp = uu____7309;
                          FStar_Syntax_Syntax.lbeff = uu____7310;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7312;
                          FStar_Syntax_Syntax.lbpos = uu____7313;_}::[]),e)
                     ->
                     let lb =
                       let uu____7338 =
                         let uu____7339 = FStar_Syntax_Subst.compress t1  in
                         uu____7339.FStar_Syntax_Syntax.n  in
                       match uu____7338 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7343) -> lb
                       | uu____7356 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7365 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7365
                         (fun def1  ->
                            ret
                              (let uu___393_7371 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___393_7371.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___393_7371.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___393_7371.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___393_7371.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___393_7371.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___393_7371.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7372 = fflb lb  in
                     bind uu____7372
                       (fun lb1  ->
                          let uu____7382 =
                            let uu____7387 =
                              let uu____7388 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7388]  in
                            FStar_Syntax_Subst.open_term uu____7387 e  in
                          match uu____7382 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7418 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7418  in
                              let uu____7419 = ff1 e1  in
                              bind uu____7419
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7460 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7460
                         (fun def  ->
                            ret
                              (let uu___394_7466 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___394_7466.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___394_7466.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___394_7466.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___394_7466.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___394_7466.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___394_7466.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7467 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7467 with
                      | (lbs1,e1) ->
                          let uu____7482 = mapM fflb lbs1  in
                          bind uu____7482
                            (fun lbs2  ->
                               let uu____7494 = ff e1  in
                               bind uu____7494
                                 (fun e2  ->
                                    let uu____7502 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7502 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7570 = ff t2  in
                     bind uu____7570
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7601 = ff t2  in
                     bind uu____7601
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7608 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___395_7615 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___395_7615.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___395_7615.FStar_Syntax_Syntax.vars)
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
            let uu____7652 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7652 with
            | (t1,lcomp,g) ->
                let uu____7664 =
                  (let uu____7667 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7667) ||
                    (let uu____7669 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7669)
                   in
                if uu____7664
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7677 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7677
                       (fun uu____7693  ->
                          match uu____7693 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7706  ->
                                    let uu____7707 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7708 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7707 uu____7708);
                               (let uu____7709 =
                                  let uu____7712 =
                                    let uu____7713 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7713 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7712
                                    opts
                                   in
                                bind uu____7709
                                  (fun uu____7716  ->
                                     let uu____7717 =
                                       bind tau
                                         (fun uu____7723  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7729  ->
                                                 let uu____7730 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7731 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7730 uu____7731);
                                            ret ut1)
                                        in
                                     focus uu____7717))))
                      in
                   let uu____7732 = trytac' rewrite_eq  in
                   bind uu____7732
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
          let uu____7930 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7930
            (fun t1  ->
               let uu____7938 =
                 f env
                   (let uu___399_7947 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___399_7947.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___399_7947.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7938
                 (fun uu____7963  ->
                    match uu____7963 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7986 =
                               let uu____7987 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7987.FStar_Syntax_Syntax.n  in
                             match uu____7986 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8024 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8024
                                   (fun uu____8049  ->
                                      match uu____8049 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8065 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8065
                                            (fun uu____8092  ->
                                               match uu____8092 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___397_8122 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___397_8122.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___397_8122.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8164 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8164 with
                                  | (bs1,t') ->
                                      let uu____8179 =
                                        let uu____8186 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8186 ctrl1 t'
                                         in
                                      bind uu____8179
                                        (fun uu____8204  ->
                                           match uu____8204 with
                                           | (t'',ctrl2) ->
                                               let uu____8219 =
                                                 let uu____8226 =
                                                   let uu___398_8229 = t4  in
                                                   let uu____8232 =
                                                     let uu____8233 =
                                                       let uu____8252 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8261 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8252,
                                                         uu____8261, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8233
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8232;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___398_8229.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___398_8229.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8226, ctrl2)  in
                                               ret uu____8219))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8314 -> ret (t3, ctrl1))))

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
              let uu____8361 = ctrl_tac_fold f env ctrl t  in
              bind uu____8361
                (fun uu____8385  ->
                   match uu____8385 with
                   | (t1,ctrl1) ->
                       let uu____8400 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8400
                         (fun uu____8427  ->
                            match uu____8427 with
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
              let uu____8511 =
                let uu____8518 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8518
                  (fun uu____8527  ->
                     let uu____8528 = ctrl t1  in
                     bind uu____8528
                       (fun res  ->
                          let uu____8551 = trivial ()  in
                          bind uu____8551 (fun uu____8559  -> ret res)))
                 in
              bind uu____8511
                (fun uu____8575  ->
                   match uu____8575 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8599 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8599 with
                          | (t2,lcomp,g) ->
                              let uu____8615 =
                                (let uu____8618 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8618) ||
                                  (let uu____8620 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8620)
                                 in
                              if uu____8615
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8633 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8633
                                   (fun uu____8653  ->
                                      match uu____8653 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8670  ->
                                                let uu____8671 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8672 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8671 uu____8672);
                                           (let uu____8673 =
                                              let uu____8676 =
                                                let uu____8677 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8677 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8676 opts
                                               in
                                            bind uu____8673
                                              (fun uu____8684  ->
                                                 let uu____8685 =
                                                   bind rewriter
                                                     (fun uu____8699  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8705  ->
                                                             let uu____8706 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8707 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8706
                                                               uu____8707);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8685)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8748 =
        bind get
          (fun ps  ->
             let uu____8758 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8758 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8795  ->
                       let uu____8796 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8796);
                  bind dismiss_all
                    (fun uu____8799  ->
                       let uu____8800 =
                         let uu____8807 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8807
                           keepGoing gt1
                          in
                       bind uu____8800
                         (fun uu____8819  ->
                            match uu____8819 with
                            | (gt',uu____8827) ->
                                (log ps
                                   (fun uu____8831  ->
                                      let uu____8832 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8832);
                                 (let uu____8833 = push_goals gs  in
                                  bind uu____8833
                                    (fun uu____8838  ->
                                       let uu____8839 =
                                         let uu____8842 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8842]  in
                                       add_goals uu____8839)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8748
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8865 =
        bind get
          (fun ps  ->
             let uu____8875 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8875 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8912  ->
                       let uu____8913 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8913);
                  bind dismiss_all
                    (fun uu____8916  ->
                       let uu____8917 =
                         let uu____8920 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8920 gt1
                          in
                       bind uu____8917
                         (fun gt'  ->
                            log ps
                              (fun uu____8928  ->
                                 let uu____8929 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8929);
                            (let uu____8930 = push_goals gs  in
                             bind uu____8930
                               (fun uu____8935  ->
                                  let uu____8936 =
                                    let uu____8939 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8939]  in
                                  add_goals uu____8936))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8865
  
let (trefl : unit -> unit tac) =
  fun uu____8950  ->
    let uu____8953 =
      let uu____8956 = cur_goal ()  in
      bind uu____8956
        (fun g  ->
           let uu____8974 =
             let uu____8979 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8979  in
           match uu____8974 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8987 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8987 with
                | (hd1,args) ->
                    let uu____9026 =
                      let uu____9039 =
                        let uu____9040 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9040.FStar_Syntax_Syntax.n  in
                      (uu____9039, args)  in
                    (match uu____9026 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9054::(l,uu____9056)::(r,uu____9058)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9105 =
                           let uu____9108 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9108 l r  in
                         bind uu____9105
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____9115 =
                                  let uu____9116 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____9116 l  in
                                let uu____9117 =
                                  let uu____9118 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____9118 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____9115 uu____9117
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____9121) ->
                         let uu____9138 =
                           let uu____9139 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9139 t  in
                         fail1 "trefl: not an equality (%s)" uu____9138))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8953
  
let (dup : unit -> unit tac) =
  fun uu____9152  ->
    let uu____9155 = cur_goal ()  in
    bind uu____9155
      (fun g  ->
         let uu____9161 =
           let uu____9168 = FStar_Tactics_Types.goal_env g  in
           let uu____9169 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9168 uu____9169  in
         bind uu____9161
           (fun uu____9178  ->
              match uu____9178 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___400_9188 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___400_9188.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___400_9188.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___400_9188.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9191  ->
                       let uu____9192 =
                         let uu____9195 = FStar_Tactics_Types.goal_env g  in
                         let uu____9196 =
                           let uu____9197 =
                             let uu____9198 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9199 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9198
                               uu____9199
                              in
                           let uu____9200 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9201 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9197 uu____9200 u
                             uu____9201
                            in
                         add_irrelevant_goal "dup equation" uu____9195
                           uu____9196 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9192
                         (fun uu____9204  ->
                            let uu____9205 = add_goals [g']  in
                            bind uu____9205 (fun uu____9209  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9216  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___401_9233 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___401_9233.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___401_9233.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___401_9233.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___401_9233.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___401_9233.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___401_9233.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___401_9233.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___401_9233.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___401_9233.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___401_9233.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___401_9233.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9234 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9243  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___402_9256 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___402_9256.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___402_9256.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___402_9256.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___402_9256.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___402_9256.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___402_9256.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___402_9256.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___402_9256.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___402_9256.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___402_9256.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___402_9256.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9263  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9270 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9290 =
      let uu____9297 = cur_goal ()  in
      bind uu____9297
        (fun g  ->
           let uu____9307 =
             let uu____9316 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9316 t  in
           bind uu____9307
             (fun uu____9344  ->
                match uu____9344 with
                | (t1,typ,guard) ->
                    let uu____9360 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9360 with
                     | (hd1,args) ->
                         let uu____9409 =
                           let uu____9424 =
                             let uu____9425 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9425.FStar_Syntax_Syntax.n  in
                           (uu____9424, args)  in
                         (match uu____9409 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9446)::(q,uu____9448)::[]) when
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
                                let uu____9502 =
                                  let uu____9503 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9503
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9502
                                 in
                              let g2 =
                                let uu____9505 =
                                  let uu____9506 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9506
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9505
                                 in
                              bind __dismiss
                                (fun uu____9513  ->
                                   let uu____9514 = add_goals [g1; g2]  in
                                   bind uu____9514
                                     (fun uu____9523  ->
                                        let uu____9524 =
                                          let uu____9529 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9530 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9529, uu____9530)  in
                                        ret uu____9524))
                          | uu____9535 ->
                              let uu____9550 =
                                let uu____9551 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9551 typ  in
                              fail1 "Not a disjunction: %s" uu____9550))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9290
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9581 =
      let uu____9584 = cur_goal ()  in
      bind uu____9584
        (fun g  ->
           FStar_Options.push ();
           (let uu____9597 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9597);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___403_9604 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___403_9604.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___403_9604.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___403_9604.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9581
  
let (top_env : unit -> env tac) =
  fun uu____9616  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9629  ->
    let uu____9632 = cur_goal ()  in
    bind uu____9632
      (fun g  ->
         let uu____9638 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9638)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9647  ->
    let uu____9650 = cur_goal ()  in
    bind uu____9650
      (fun g  ->
         let uu____9656 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9656)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9665  ->
    let uu____9668 = cur_goal ()  in
    bind uu____9668
      (fun g  ->
         let uu____9674 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9674)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9691 =
        mlog
          (fun uu____9696  ->
             let uu____9697 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9697)
          (fun uu____9700  ->
             let uu____9701 = cur_goal ()  in
             bind uu____9701
               (fun goal  ->
                  let env =
                    let uu____9709 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9709 ty  in
                  let uu____9710 = __tc env tm  in
                  bind uu____9710
                    (fun uu____9729  ->
                       match uu____9729 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9743  ->
                                let uu____9744 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9744)
                             (fun uu____9746  ->
                                mlog
                                  (fun uu____9749  ->
                                     let uu____9750 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9750)
                                  (fun uu____9753  ->
                                     let uu____9754 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9754
                                       (fun uu____9758  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9691
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9781 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9787 =
              let uu____9794 =
                let uu____9795 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9795
                 in
              new_uvar "uvar_env.2" env uu____9794  in
            bind uu____9787
              (fun uu____9811  ->
                 match uu____9811 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9781
        (fun typ  ->
           let uu____9823 = new_uvar "uvar_env" env typ  in
           bind uu____9823
             (fun uu____9837  -> match uu____9837 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9855 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9874 -> g.FStar_Tactics_Types.opts
             | uu____9877 -> FStar_Options.peek ()  in
           let uu____9880 = FStar_Syntax_Util.head_and_args t  in
           match uu____9880 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9900);
                FStar_Syntax_Syntax.pos = uu____9901;
                FStar_Syntax_Syntax.vars = uu____9902;_},uu____9903)
               ->
               let env1 =
                 let uu___404_9945 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___404_9945.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___404_9945.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___404_9945.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___404_9945.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___404_9945.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___404_9945.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___404_9945.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___404_9945.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___404_9945.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___404_9945.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___404_9945.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___404_9945.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___404_9945.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___404_9945.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___404_9945.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___404_9945.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___404_9945.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___404_9945.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___404_9945.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___404_9945.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___404_9945.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___404_9945.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___404_9945.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___404_9945.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___404_9945.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___404_9945.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___404_9945.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___404_9945.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___404_9945.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___404_9945.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___404_9945.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___404_9945.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___404_9945.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___404_9945.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___404_9945.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___404_9945.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___404_9945.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___404_9945.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___404_9945.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___404_9945.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9947 =
                 let uu____9950 = bnorm_goal g  in [uu____9950]  in
               add_goals uu____9947
           | uu____9951 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9855
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____10000 = if b then t2 else ret false  in
             bind uu____10000 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10011 = trytac comp  in
      bind uu____10011
        (fun uu___346_10019  ->
           match uu___346_10019 with
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
        let uu____10045 =
          bind get
            (fun ps  ->
               let uu____10051 = __tc e t1  in
               bind uu____10051
                 (fun uu____10071  ->
                    match uu____10071 with
                    | (t11,ty1,g1) ->
                        let uu____10083 = __tc e t2  in
                        bind uu____10083
                          (fun uu____10103  ->
                             match uu____10103 with
                             | (t21,ty2,g2) ->
                                 let uu____10115 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10115
                                   (fun uu____10120  ->
                                      let uu____10121 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10121
                                        (fun uu____10127  ->
                                           let uu____10128 =
                                             do_unify e ty1 ty2  in
                                           let uu____10131 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10128 uu____10131)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10045
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10164  ->
             let uu____10165 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10165
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
        (fun uu____10186  ->
           let uu____10187 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10187)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10197 =
      mlog
        (fun uu____10202  ->
           let uu____10203 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10203)
        (fun uu____10206  ->
           let uu____10207 = cur_goal ()  in
           bind uu____10207
             (fun g  ->
                let uu____10213 =
                  let uu____10222 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10222 ty  in
                bind uu____10213
                  (fun uu____10234  ->
                     match uu____10234 with
                     | (ty1,uu____10244,guard) ->
                         let uu____10246 =
                           let uu____10249 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10249 guard  in
                         bind uu____10246
                           (fun uu____10252  ->
                              let uu____10253 =
                                let uu____10256 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10257 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10256 uu____10257 ty1  in
                              bind uu____10253
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10263 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10263
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
                                        let uu____10269 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10270 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10269
                                          uu____10270
                                         in
                                      let nty =
                                        let uu____10272 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10272 ty1  in
                                      let uu____10273 =
                                        let uu____10276 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10276 ng nty  in
                                      bind uu____10273
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10282 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10282
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10197
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10304::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10332 = init xs  in x :: uu____10332
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____10344 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____10352) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10417 = last args  in
          (match uu____10417 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10447 =
                 let uu____10448 =
                   let uu____10453 =
                     let uu____10454 =
                       let uu____10459 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10459  in
                     uu____10454 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10453, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10448  in
               FStar_All.pipe_left ret uu____10447)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10472,uu____10473) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10525 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10525 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10566 =
                      let uu____10567 =
                        let uu____10572 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10572)  in
                      FStar_Reflection_Data.Tv_Abs uu____10567  in
                    FStar_All.pipe_left ret uu____10566))
      | FStar_Syntax_Syntax.Tm_type uu____10575 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10599 ->
          let uu____10614 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10614 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10644 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10644 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10697 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10709 =
            let uu____10710 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10710  in
          FStar_All.pipe_left ret uu____10709
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10731 =
            let uu____10732 =
              let uu____10737 =
                let uu____10738 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10738  in
              (uu____10737, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10732  in
          FStar_All.pipe_left ret uu____10731
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10772 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10777 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10777 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10830 ->
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
             | FStar_Util.Inr uu____10864 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10868 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10868 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10888 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10892 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10946 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10946
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10965 =
                  let uu____10972 =
                    FStar_List.map
                      (fun uu____10984  ->
                         match uu____10984 with
                         | (p1,uu____10992) -> inspect_pat p1) ps
                     in
                  (fv, uu____10972)  in
                FStar_Reflection_Data.Pat_Cons uu____10965
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
              (fun uu___347_11086  ->
                 match uu___347_11086 with
                 | (pat,uu____11108,t4) ->
                     let uu____11126 = inspect_pat pat  in (uu____11126, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____11135 ->
          ((let uu____11137 =
              let uu____11142 =
                let uu____11143 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____11144 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____11143 uu____11144
                 in
              (FStar_Errors.Warning_CantInspect, uu____11142)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____11137);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____10344
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____11157 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____11157
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____11161 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____11161
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____11165 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____11165
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____11172 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____11172
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____11197 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____11197
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____11214 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____11214
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____11233 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____11233
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11237 =
          let uu____11238 =
            let uu____11245 =
              let uu____11246 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____11246  in
            FStar_Syntax_Syntax.mk uu____11245  in
          uu____11238 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____11237
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____11254 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11254
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____11263 =
          let uu____11264 =
            let uu____11271 =
              let uu____11272 =
                let uu____11285 =
                  let uu____11288 =
                    let uu____11289 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____11289]  in
                  FStar_Syntax_Subst.close uu____11288 t2  in
                ((false, [lb]), uu____11285)  in
              FStar_Syntax_Syntax.Tm_let uu____11272  in
            FStar_Syntax_Syntax.mk uu____11271  in
          uu____11264 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____11263
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____11329 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____11329 with
         | (lbs,body) ->
             let uu____11344 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____11344)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11378 =
                let uu____11379 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____11379  in
              FStar_All.pipe_left wrap uu____11378
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____11386 =
                let uu____11387 =
                  let uu____11400 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____11416 = pack_pat p1  in
                         (uu____11416, false)) ps
                     in
                  (fv, uu____11400)  in
                FStar_Syntax_Syntax.Pat_cons uu____11387  in
              FStar_All.pipe_left wrap uu____11386
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
            (fun uu___348_11462  ->
               match uu___348_11462 with
               | (pat,t1) ->
                   let uu____11479 = pack_pat pat  in
                   (uu____11479, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11527 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11527
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11555 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11555
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11601 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11601
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11640 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11640
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11661 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11661 with
      | (u,ctx_uvars,g_u) ->
          let uu____11693 = FStar_List.hd ctx_uvars  in
          (match uu____11693 with
           | (ctx_uvar,uu____11707) ->
               let g =
                 let uu____11709 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11709 false
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
        let uu____11729 = goal_of_goal_ty env typ  in
        match uu____11729 with
        | (g,g_u) ->
            let ps =
              let uu____11741 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11741
              }  in
            let uu____11746 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11746)
  