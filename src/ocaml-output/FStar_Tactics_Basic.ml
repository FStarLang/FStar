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
                 let uu___347_1033 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___347_1033.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___347_1033.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___347_1033.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___347_1033.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___347_1033.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___347_1033.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___347_1033.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___347_1033.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___347_1033.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___347_1033.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___347_1033.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___352_1309 = ps  in
         let uu____1310 =
           FStar_List.filter
             (fun g  ->
                let uu____1316 = check_goal_solved g  in
                FStar_Option.isNone uu____1316) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___352_1309.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___352_1309.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___352_1309.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1310;
           FStar_Tactics_Types.smt_goals =
             (uu___352_1309.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___352_1309.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___352_1309.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___352_1309.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___352_1309.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___352_1309.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___352_1309.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___352_1309.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___353_1364 = p  in
         let uu____1365 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___353_1364.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___353_1364.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___353_1364.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1365;
           FStar_Tactics_Types.smt_goals =
             (uu___353_1364.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___353_1364.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___353_1364.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___353_1364.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___353_1364.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___353_1364.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___353_1364.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___353_1364.FStar_Tactics_Types.tac_verb_dbg)
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
         (let uu___354_1455 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___354_1455.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___354_1455.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___354_1455.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___354_1455.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___354_1455.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___354_1455.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___354_1455.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___354_1455.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___354_1455.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___354_1455.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___354_1455.FStar_Tactics_Types.tac_verb_dbg)
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
           (let uu___355_1622 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___355_1622.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___355_1622.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___355_1622.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___355_1622.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___355_1622.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___355_1622.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___355_1622.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___355_1622.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___355_1622.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___355_1622.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___355_1622.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___356_1642 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___356_1642.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___356_1642.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___356_1642.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___356_1642.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___356_1642.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___356_1642.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___356_1642.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___356_1642.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___356_1642.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___356_1642.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___356_1642.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1662 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1662.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1662.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1662.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___357_1662.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_1662.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1662.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1662.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1662.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1662.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1662.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1662.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_1682 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1682.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1682.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_1682.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___358_1682.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___358_1682.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1682.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1682.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1682.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1682.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1682.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1682.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1693  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___359_1707 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1707.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1707.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1707.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___359_1707.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1707.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1707.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1707.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1707.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1707.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1707.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1707.FStar_Tactics_Types.tac_verb_dbg)
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
           let uu___360_1929 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___360_1929.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___360_1929.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___360_1929.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___360_1929.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___360_1929.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___360_1929.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___360_1929.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___360_1929.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___360_1929.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___360_1929.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___360_1929.FStar_Tactics_Types.tac_verb_dbg)
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
                  let uu___361_2094 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___361_2094.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___361_2094.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___361_2094.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___361_2094.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___361_2094.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___361_2094.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___361_2094.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___361_2094.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___361_2094.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___361_2094.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___361_2094.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___361_2094.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___361_2094.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___361_2094.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___361_2094.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___361_2094.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___361_2094.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___361_2094.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___361_2094.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___361_2094.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___361_2094.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___361_2094.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___361_2094.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___361_2094.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___361_2094.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___361_2094.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___361_2094.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___361_2094.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___361_2094.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___361_2094.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___361_2094.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___361_2094.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___361_2094.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___361_2094.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___361_2094.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___361_2094.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___361_2094.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___361_2094.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___361_2094.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___361_2094.FStar_TypeChecker_Env.dep_graph)
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
           (let uu___364_2202 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___364_2202.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___364_2202.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___364_2202.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___364_2202.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___364_2202.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___364_2202.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___364_2202.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___364_2202.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___364_2202.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___364_2202.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___364_2202.FStar_Tactics_Types.tac_verb_dbg)
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
    (fun uu___337_2259  ->
       match uu___337_2259 with
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
                                   let uu___365_2308 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___365_2308.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___365_2308.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___365_2308.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2309 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2309
                              (fun goal  ->
                                 let goal1 =
                                   let uu___366_2316 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___366_2316.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___366_2316.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___366_2316.FStar_Tactics_Types.opts);
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
                           (let uu___369_2517 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___369_2517.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___369_2517.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___369_2517.FStar_Tactics_Types.opts);
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
                        let uu___370_2707 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___370_2707.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___370_2707.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___370_2707.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___370_2707.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___370_2707.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___370_2707.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___370_2707.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___370_2707.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___370_2707.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___370_2707.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2708 = set lp  in
                      bind uu____2708
                        (fun uu____2716  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___371_2732 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___371_2732.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___371_2732.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___371_2732.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___371_2732.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___371_2732.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___371_2732.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___371_2732.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___371_2732.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___371_2732.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___371_2732.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2733 = set rp  in
                                     bind uu____2733
                                       (fun uu____2741  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___372_2757 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___372_2757.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___372_2757.FStar_Tactics_Types.tac_verb_dbg)
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
                  let uu____2985 = new_uvar "intro" env' typ'  in
                  bind uu____2985
                    (fun uu____3001  ->
                       match uu____3001 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3021 = set_solution goal sol  in
                           bind uu____3021
                             (fun uu____3027  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3029 =
                                  let uu____3032 = bnorm_goal g  in
                                  replace_cur uu____3032  in
                                bind uu____3029 (fun uu____3034  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3039 =
                 let uu____3040 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3041 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3040 uu____3041  in
               fail1 "goal is not an arrow (%s)" uu____3039)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2941
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3056  ->
    let uu____3063 = cur_goal ()  in
    bind uu____3063
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3080 =
            let uu____3087 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3087  in
          match uu____3080 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3100 =
                let uu____3101 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3101  in
              if uu____3100
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3114 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3114
                    in
                 let bs =
                   let uu____3122 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3122; b]  in
                 let env' =
                   let uu____3140 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3140 bs  in
                 let uu____3141 =
                   let uu____3148 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3148  in
                 bind uu____3141
                   (fun uu____3167  ->
                      match uu____3167 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3181 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3184 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3181
                              FStar_Parser_Const.effect_Tot_lid uu____3184 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3198 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3198 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3220 =
                                   let uu____3221 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3221.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3220
                                  in
                               let uu____3234 = set_solution goal tm  in
                               bind uu____3234
                                 (fun uu____3243  ->
                                    let uu____3244 =
                                      let uu____3247 =
                                        bnorm_goal
                                          (let uu___375_3250 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___375_3250.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___375_3250.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___375_3250.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3247  in
                                    bind uu____3244
                                      (fun uu____3257  ->
                                         let uu____3258 =
                                           let uu____3263 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3263, b)  in
                                         ret uu____3258)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3272 =
                let uu____3273 = FStar_Tactics_Types.goal_env goal  in
                let uu____3274 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3273 uu____3274  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3272))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3292 = cur_goal ()  in
    bind uu____3292
      (fun goal  ->
         mlog
           (fun uu____3299  ->
              let uu____3300 =
                let uu____3301 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3301  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3300)
           (fun uu____3306  ->
              let steps =
                let uu____3310 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3310
                 in
              let t =
                let uu____3314 = FStar_Tactics_Types.goal_env goal  in
                let uu____3315 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3314 uu____3315  in
              let uu____3316 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3316))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3340 =
          mlog
            (fun uu____3345  ->
               let uu____3346 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3346)
            (fun uu____3348  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3354 -> g.FStar_Tactics_Types.opts
                      | uu____3357 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3362  ->
                         let uu____3363 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3363)
                      (fun uu____3366  ->
                         let uu____3367 = __tc e t  in
                         bind uu____3367
                           (fun uu____3388  ->
                              match uu____3388 with
                              | (t1,uu____3398,uu____3399) ->
                                  let steps =
                                    let uu____3403 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3403
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3340
  
let (refine_intro : unit -> unit tac) =
  fun uu____3417  ->
    let uu____3420 =
      let uu____3423 = cur_goal ()  in
      bind uu____3423
        (fun g  ->
           let uu____3430 =
             let uu____3441 = FStar_Tactics_Types.goal_env g  in
             let uu____3442 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3441 uu____3442
              in
           match uu____3430 with
           | (uu____3445,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3470 =
                 let uu____3475 =
                   let uu____3480 =
                     let uu____3481 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3481]  in
                   FStar_Syntax_Subst.open_term uu____3480 phi  in
                 match uu____3475 with
                 | (bvs,phi1) ->
                     let uu____3500 =
                       let uu____3501 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3501  in
                     (uu____3500, phi1)
                  in
               (match uu____3470 with
                | (bv1,phi1) ->
                    let uu____3514 =
                      let uu____3517 = FStar_Tactics_Types.goal_env g  in
                      let uu____3518 =
                        let uu____3519 =
                          let uu____3522 =
                            let uu____3523 =
                              let uu____3530 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3530)  in
                            FStar_Syntax_Syntax.NT uu____3523  in
                          [uu____3522]  in
                        FStar_Syntax_Subst.subst uu____3519 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3517
                        uu____3518 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3514
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3538  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3420
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3557 = cur_goal ()  in
      bind uu____3557
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3565 = FStar_Tactics_Types.goal_env goal  in
               let uu____3566 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3565 uu____3566
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3568 = __tc env t  in
           bind uu____3568
             (fun uu____3587  ->
                match uu____3587 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3602  ->
                         let uu____3603 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3604 =
                           let uu____3605 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3605
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3603 uu____3604)
                      (fun uu____3608  ->
                         let uu____3609 =
                           let uu____3612 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3612 guard  in
                         bind uu____3609
                           (fun uu____3614  ->
                              mlog
                                (fun uu____3618  ->
                                   let uu____3619 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3620 =
                                     let uu____3621 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3621
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3619 uu____3620)
                                (fun uu____3624  ->
                                   let uu____3625 =
                                     let uu____3628 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3629 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3628 typ uu____3629  in
                                   bind uu____3625
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3635 =
                                             let uu____3636 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3636 t1  in
                                           let uu____3637 =
                                             let uu____3638 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3638 typ  in
                                           let uu____3639 =
                                             let uu____3640 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3641 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3640 uu____3641  in
                                           let uu____3642 =
                                             let uu____3643 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3644 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3643 uu____3644  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3635 uu____3637 uu____3639
                                             uu____3642)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3659 =
        mlog
          (fun uu____3664  ->
             let uu____3665 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3665)
          (fun uu____3668  ->
             let uu____3669 =
               let uu____3676 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3676  in
             bind uu____3669
               (fun uu___339_3685  ->
                  match uu___339_3685 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3695  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3698  ->
                           let uu____3699 =
                             let uu____3706 =
                               let uu____3709 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3709
                                 (fun uu____3714  ->
                                    let uu____3715 = refine_intro ()  in
                                    bind uu____3715
                                      (fun uu____3719  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3706  in
                           bind uu____3699
                             (fun uu___338_3726  ->
                                match uu___338_3726 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3734 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3659
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3784 = f x  in
          bind uu____3784
            (fun y  ->
               let uu____3792 = mapM f xs  in
               bind uu____3792 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3863 = do_unify e ty1 ty2  in
          bind uu____3863
            (fun uu___340_3875  ->
               if uu___340_3875
               then ret acc
               else
                 (let uu____3894 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3894 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3915 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3916 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3915
                        uu____3916
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3931 =
                        let uu____3932 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3932  in
                      if uu____3931
                      then fail "Codomain is effectful"
                      else
                        (let uu____3952 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3952
                           (fun uu____3976  ->
                              match uu____3976 with
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
      let uu____4058 =
        mlog
          (fun uu____4063  ->
             let uu____4064 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4064)
          (fun uu____4067  ->
             let uu____4068 = cur_goal ()  in
             bind uu____4068
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4076 = __tc e tm  in
                  bind uu____4076
                    (fun uu____4097  ->
                       match uu____4097 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4110 =
                             let uu____4121 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4121  in
                           bind uu____4110
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4162  ->
                                       fun w  ->
                                         match uu____4162 with
                                         | (uvt,q,uu____4178) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4200 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4217  ->
                                       fun s  ->
                                         match uu____4217 with
                                         | (uu____4229,uu____4230,uv) ->
                                             let uu____4232 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4232) uvs uu____4200
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4241 = solve' goal w  in
                                bind uu____4241
                                  (fun uu____4246  ->
                                     let uu____4247 =
                                       mapM
                                         (fun uu____4264  ->
                                            match uu____4264 with
                                            | (uvt,q,uv) ->
                                                let uu____4276 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4276 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4281 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4282 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4282
                                                     then ret ()
                                                     else
                                                       (let uu____4286 =
                                                          let uu____4289 =
                                                            bnorm_goal
                                                              (let uu___376_4292
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___376_4292.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___376_4292.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4289]  in
                                                        add_goals uu____4286)))
                                         uvs
                                        in
                                     bind uu____4247
                                       (fun uu____4296  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4058
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4321 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4321
    then
      let uu____4328 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4343 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4382 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4328 with
      | (pre,post) ->
          let post1 =
            let uu____4412 =
              let uu____4421 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4421]  in
            FStar_Syntax_Util.mk_app post uu____4412  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4445 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4445
       then
         let uu____4452 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4452
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4485 =
      let uu____4488 =
        mlog
          (fun uu____4493  ->
             let uu____4494 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4494)
          (fun uu____4498  ->
             let is_unit_t t =
               let uu____4505 =
                 let uu____4506 = FStar_Syntax_Subst.compress t  in
                 uu____4506.FStar_Syntax_Syntax.n  in
               match uu____4505 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4510 -> false  in
             let uu____4511 = cur_goal ()  in
             bind uu____4511
               (fun goal  ->
                  let uu____4517 =
                    let uu____4526 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4526 tm  in
                  bind uu____4517
                    (fun uu____4541  ->
                       match uu____4541 with
                       | (tm1,t,guard) ->
                           let uu____4553 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4553 with
                            | (bs,comp) ->
                                let uu____4580 = lemma_or_sq comp  in
                                (match uu____4580 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4599 =
                                       FStar_List.fold_left
                                         (fun uu____4641  ->
                                            fun uu____4642  ->
                                              match (uu____4641, uu____4642)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4733 =
                                                    is_unit_t b_t  in
                                                  if uu____4733
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4763 =
                                                       let uu____4776 =
                                                         let uu____4777 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4777.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4780 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4776
                                                         uu____4780 b_t
                                                        in
                                                     match uu____4763 with
                                                     | (u,uu____4796,g_u) ->
                                                         let uu____4810 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4810,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4599 with
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
                                          let uu____4871 =
                                            let uu____4874 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4875 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4876 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4874 uu____4875
                                              uu____4876
                                             in
                                          bind uu____4871
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4884 =
                                                   let uu____4885 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4885 tm1  in
                                                 let uu____4886 =
                                                   let uu____4887 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4888 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4887 uu____4888
                                                    in
                                                 let uu____4889 =
                                                   let uu____4890 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4891 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4890 uu____4891
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4884 uu____4886
                                                   uu____4889
                                               else
                                                 (let uu____4893 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4893
                                                    (fun uu____4898  ->
                                                       let uu____4899 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4899
                                                         (fun uu____4907  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4932
                                                                  =
                                                                  let uu____4935
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4935
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4932
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
                                                                   let uu____4970
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4970)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4986
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4986
                                                              with
                                                              | (hd1,uu____5002)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5024)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5041
                                                                    -> false)
                                                               in
                                                            let uu____5042 =
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
                                                                    let uu____5090
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5090
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5116)
                                                                    ->
                                                                    let uu____5137
                                                                    =
                                                                    let uu____5138
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5138.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5137
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5152)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___377_5172
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___377_5172.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___377_5172.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___377_5172.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5185
                                                                    ->
                                                                    let env =
                                                                    let uu___378_5187
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___378_5187.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5189
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5189
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
                                                                    let uu____5192
                                                                    =
                                                                    let uu____5199
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5199
                                                                    term1  in
                                                                    match uu____5192
                                                                    with
                                                                    | 
                                                                    (uu____5200,uu____5201,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5203
                                                                    =
                                                                    let uu____5208
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5208
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5203
                                                                    (fun
                                                                    uu___341_5220
                                                                     ->
                                                                    match uu___341_5220
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
                                                            bind uu____5042
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5288
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5288
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5310
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5310
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5371
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5371
                                                                    then
                                                                    let uu____5374
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5374
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
                                                                    let uu____5388
                                                                    =
                                                                    let uu____5389
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5389
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5388)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5390
                                                                   =
                                                                   let uu____5393
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5393
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5390
                                                                   (fun
                                                                    uu____5396
                                                                     ->
                                                                    let uu____5397
                                                                    =
                                                                    let uu____5400
                                                                    =
                                                                    let uu____5401
                                                                    =
                                                                    let uu____5402
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5403
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5402
                                                                    uu____5403
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5401
                                                                     in
                                                                    if
                                                                    uu____5400
                                                                    then
                                                                    let uu____5406
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5406
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5397
                                                                    (fun
                                                                    uu____5410
                                                                     ->
                                                                    let uu____5411
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5411
                                                                    (fun
                                                                    uu____5415
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4488  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4485
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5437 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5437 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5447::(e1,uu____5449)::(e2,uu____5451)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5494 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5518 = destruct_eq' typ  in
    match uu____5518 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5548 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5548 with
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
        let uu____5610 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5610 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5658 = aux e'  in
               FStar_Util.map_opt uu____5658
                 (fun uu____5682  ->
                    match uu____5682 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5703 = aux e  in
      FStar_Util.map_opt uu____5703
        (fun uu____5727  ->
           match uu____5727 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5794 =
            let uu____5803 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5803  in
          FStar_Util.map_opt uu____5794
            (fun uu____5818  ->
               match uu____5818 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___379_5837 = bv  in
                     let uu____5838 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___379_5837.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___379_5837.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5838
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___380_5846 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5847 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5854 =
                       let uu____5857 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5857  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___380_5846.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5847;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5854;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___380_5846.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___380_5846.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___380_5846.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___381_5858 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___381_5858.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___381_5858.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___381_5858.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5868 =
      let uu____5871 = cur_goal ()  in
      bind uu____5871
        (fun goal  ->
           let uu____5879 = h  in
           match uu____5879 with
           | (bv,uu____5883) ->
               mlog
                 (fun uu____5887  ->
                    let uu____5888 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5889 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5888
                      uu____5889)
                 (fun uu____5892  ->
                    let uu____5893 =
                      let uu____5902 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5902  in
                    match uu____5893 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5923 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5923 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5938 =
                               let uu____5939 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5939.FStar_Syntax_Syntax.n  in
                             (match uu____5938 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___382_5956 = bv1  in
                                    let uu____5957 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___382_5956.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___382_5956.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5957
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___383_5965 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5966 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5973 =
                                      let uu____5976 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____5976
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___383_5965.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5966;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5973;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___383_5965.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___383_5965.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___383_5965.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___384_5979 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___384_5979.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___384_5979.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___384_5979.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____5980 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5981 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5868
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6006 =
        let uu____6009 = cur_goal ()  in
        bind uu____6009
          (fun goal  ->
             let uu____6020 = b  in
             match uu____6020 with
             | (bv,uu____6024) ->
                 let bv' =
                   let uu____6026 =
                     let uu___385_6027 = bv  in
                     let uu____6028 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6028;
                       FStar_Syntax_Syntax.index =
                         (uu___385_6027.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___385_6027.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6026  in
                 let s1 =
                   let uu____6032 =
                     let uu____6033 =
                       let uu____6040 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6040)  in
                     FStar_Syntax_Syntax.NT uu____6033  in
                   [uu____6032]  in
                 let uu____6045 = subst_goal bv bv' s1 goal  in
                 (match uu____6045 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6006
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6064 =
      let uu____6067 = cur_goal ()  in
      bind uu____6067
        (fun goal  ->
           let uu____6076 = b  in
           match uu____6076 with
           | (bv,uu____6080) ->
               let uu____6081 =
                 let uu____6090 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6090  in
               (match uu____6081 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6111 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6111 with
                     | (ty,u) ->
                         let uu____6120 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6120
                           (fun uu____6138  ->
                              match uu____6138 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___386_6148 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___386_6148.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___386_6148.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6152 =
                                      let uu____6153 =
                                        let uu____6160 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6160)  in
                                      FStar_Syntax_Syntax.NT uu____6153  in
                                    [uu____6152]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___387_6172 = b1  in
                                         let uu____6173 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___387_6172.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___387_6172.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6173
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6180  ->
                                       let new_goal =
                                         let uu____6182 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6183 =
                                           let uu____6184 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6184
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6182 uu____6183
                                          in
                                       let uu____6185 = add_goals [new_goal]
                                          in
                                       bind uu____6185
                                         (fun uu____6190  ->
                                            let uu____6191 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6191
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6064
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6214 =
        let uu____6217 = cur_goal ()  in
        bind uu____6217
          (fun goal  ->
             let uu____6226 = b  in
             match uu____6226 with
             | (bv,uu____6230) ->
                 let uu____6231 =
                   let uu____6240 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6240  in
                 (match uu____6231 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6264 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6264
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___388_6269 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___388_6269.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___388_6269.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6271 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6271))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6214
  
let (revert : unit -> unit tac) =
  fun uu____6282  ->
    let uu____6285 = cur_goal ()  in
    bind uu____6285
      (fun goal  ->
         let uu____6291 =
           let uu____6298 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6298  in
         match uu____6291 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6314 =
                 let uu____6317 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6317  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6314
                in
             let uu____6326 = new_uvar "revert" env' typ'  in
             bind uu____6326
               (fun uu____6341  ->
                  match uu____6341 with
                  | (r,u_r) ->
                      let uu____6350 =
                        let uu____6353 =
                          let uu____6354 =
                            let uu____6355 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6355.FStar_Syntax_Syntax.pos  in
                          let uu____6358 =
                            let uu____6363 =
                              let uu____6364 =
                                let uu____6371 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6371  in
                              [uu____6364]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6363  in
                          uu____6358 FStar_Pervasives_Native.None uu____6354
                           in
                        set_solution goal uu____6353  in
                      bind uu____6350
                        (fun uu____6388  ->
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
      let uu____6400 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6400
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6413 = cur_goal ()  in
    bind uu____6413
      (fun goal  ->
         mlog
           (fun uu____6421  ->
              let uu____6422 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6423 =
                let uu____6424 =
                  let uu____6425 =
                    let uu____6432 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6432  in
                  FStar_All.pipe_right uu____6425 FStar_List.length  in
                FStar_All.pipe_right uu____6424 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6422 uu____6423)
           (fun uu____6445  ->
              let uu____6446 =
                let uu____6455 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6455  in
              match uu____6446 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6494 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6494
                        then
                          let uu____6497 =
                            let uu____6498 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6498
                             in
                          fail uu____6497
                        else check1 bvs2
                     in
                  let uu____6500 =
                    let uu____6501 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6501  in
                  if uu____6500
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6505 = check1 bvs  in
                     bind uu____6505
                       (fun uu____6511  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6513 =
                            let uu____6520 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6520  in
                          bind uu____6513
                            (fun uu____6529  ->
                               match uu____6529 with
                               | (ut,uvar_ut) ->
                                   let uu____6538 = set_solution goal ut  in
                                   bind uu____6538
                                     (fun uu____6543  ->
                                        let uu____6544 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6544))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6551  ->
    let uu____6554 = cur_goal ()  in
    bind uu____6554
      (fun goal  ->
         let uu____6560 =
           let uu____6567 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6567  in
         match uu____6560 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6575) ->
             let uu____6580 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6580)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6590 = cur_goal ()  in
    bind uu____6590
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6600 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6600  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6603  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6613 = cur_goal ()  in
    bind uu____6613
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6623 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6623  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6626  -> add_goals [g']))
  
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
            let uu____6666 = FStar_Syntax_Subst.compress t  in
            uu____6666.FStar_Syntax_Syntax.n  in
          let uu____6669 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___392_6675 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___392_6675.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___392_6675.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6669
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6691 =
                   let uu____6692 = FStar_Syntax_Subst.compress t1  in
                   uu____6692.FStar_Syntax_Syntax.n  in
                 match uu____6691 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6719 = ff hd1  in
                     bind uu____6719
                       (fun hd2  ->
                          let fa uu____6741 =
                            match uu____6741 with
                            | (a,q) ->
                                let uu____6754 = ff a  in
                                bind uu____6754 (fun a1  -> ret (a1, q))
                             in
                          let uu____6767 = mapM fa args  in
                          bind uu____6767
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6833 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6833 with
                      | (bs1,t') ->
                          let uu____6842 =
                            let uu____6845 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6845 t'  in
                          bind uu____6842
                            (fun t''  ->
                               let uu____6849 =
                                 let uu____6850 =
                                   let uu____6867 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6874 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6867, uu____6874, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6850  in
                               ret uu____6849))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6943 = ff hd1  in
                     bind uu____6943
                       (fun hd2  ->
                          let ffb br =
                            let uu____6958 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6958 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6990 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6990  in
                                let uu____6991 = ff1 e  in
                                bind uu____6991
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7006 = mapM ffb brs  in
                          bind uu____7006
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7050;
                          FStar_Syntax_Syntax.lbtyp = uu____7051;
                          FStar_Syntax_Syntax.lbeff = uu____7052;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7054;
                          FStar_Syntax_Syntax.lbpos = uu____7055;_}::[]),e)
                     ->
                     let lb =
                       let uu____7080 =
                         let uu____7081 = FStar_Syntax_Subst.compress t1  in
                         uu____7081.FStar_Syntax_Syntax.n  in
                       match uu____7080 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7085) -> lb
                       | uu____7098 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7107 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7107
                         (fun def1  ->
                            ret
                              (let uu___389_7113 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___389_7113.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___389_7113.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___389_7113.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___389_7113.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___389_7113.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___389_7113.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7114 = fflb lb  in
                     bind uu____7114
                       (fun lb1  ->
                          let uu____7124 =
                            let uu____7129 =
                              let uu____7130 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7130]  in
                            FStar_Syntax_Subst.open_term uu____7129 e  in
                          match uu____7124 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7154 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7154  in
                              let uu____7155 = ff1 e1  in
                              bind uu____7155
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7196 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7196
                         (fun def  ->
                            ret
                              (let uu___390_7202 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___390_7202.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___390_7202.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___390_7202.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___390_7202.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___390_7202.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___390_7202.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7203 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7203 with
                      | (lbs1,e1) ->
                          let uu____7218 = mapM fflb lbs1  in
                          bind uu____7218
                            (fun lbs2  ->
                               let uu____7230 = ff e1  in
                               bind uu____7230
                                 (fun e2  ->
                                    let uu____7238 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7238 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7306 = ff t2  in
                     bind uu____7306
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7337 = ff t2  in
                     bind uu____7337
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7344 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___391_7351 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___391_7351.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___391_7351.FStar_Syntax_Syntax.vars)
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
            let uu____7388 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7388 with
            | (t1,lcomp,g) ->
                let uu____7400 =
                  (let uu____7403 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7403) ||
                    (let uu____7405 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7405)
                   in
                if uu____7400
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7413 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7413
                       (fun uu____7429  ->
                          match uu____7429 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7442  ->
                                    let uu____7443 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7444 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7443 uu____7444);
                               (let uu____7445 =
                                  let uu____7448 =
                                    let uu____7449 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7449 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7448
                                    opts
                                   in
                                bind uu____7445
                                  (fun uu____7452  ->
                                     let uu____7453 =
                                       bind tau
                                         (fun uu____7459  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7465  ->
                                                 let uu____7466 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7467 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7466 uu____7467);
                                            ret ut1)
                                        in
                                     focus uu____7453))))
                      in
                   let uu____7468 = trytac' rewrite_eq  in
                   bind uu____7468
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
          let uu____7666 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7666
            (fun t1  ->
               let uu____7674 =
                 f env
                   (let uu___395_7683 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___395_7683.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___395_7683.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7674
                 (fun uu____7699  ->
                    match uu____7699 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7722 =
                               let uu____7723 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7723.FStar_Syntax_Syntax.n  in
                             match uu____7722 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7756 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7756
                                   (fun uu____7781  ->
                                      match uu____7781 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7797 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7797
                                            (fun uu____7824  ->
                                               match uu____7824 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___393_7854 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___393_7854.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___393_7854.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7890 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7890 with
                                  | (bs1,t') ->
                                      let uu____7905 =
                                        let uu____7912 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7912 ctrl1 t'
                                         in
                                      bind uu____7905
                                        (fun uu____7930  ->
                                           match uu____7930 with
                                           | (t'',ctrl2) ->
                                               let uu____7945 =
                                                 let uu____7952 =
                                                   let uu___394_7955 = t4  in
                                                   let uu____7958 =
                                                     let uu____7959 =
                                                       let uu____7976 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7983 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7976,
                                                         uu____7983, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7959
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7958;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___394_7955.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___394_7955.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7952, ctrl2)  in
                                               ret uu____7945))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8030 -> ret (t3, ctrl1))))

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
              let uu____8073 = ctrl_tac_fold f env ctrl t  in
              bind uu____8073
                (fun uu____8097  ->
                   match uu____8097 with
                   | (t1,ctrl1) ->
                       let uu____8112 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8112
                         (fun uu____8139  ->
                            match uu____8139 with
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
              let uu____8221 =
                let uu____8228 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8228
                  (fun uu____8237  ->
                     let uu____8238 = ctrl t1  in
                     bind uu____8238
                       (fun res  ->
                          let uu____8261 = trivial ()  in
                          bind uu____8261 (fun uu____8269  -> ret res)))
                 in
              bind uu____8221
                (fun uu____8285  ->
                   match uu____8285 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8309 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8309 with
                          | (t2,lcomp,g) ->
                              let uu____8325 =
                                (let uu____8328 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8328) ||
                                  (let uu____8330 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8330)
                                 in
                              if uu____8325
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8343 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8343
                                   (fun uu____8363  ->
                                      match uu____8363 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8380  ->
                                                let uu____8381 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8382 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8381 uu____8382);
                                           (let uu____8383 =
                                              let uu____8386 =
                                                let uu____8387 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8387 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8386 opts
                                               in
                                            bind uu____8383
                                              (fun uu____8394  ->
                                                 let uu____8395 =
                                                   bind rewriter
                                                     (fun uu____8409  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8415  ->
                                                             let uu____8416 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8417 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8416
                                                               uu____8417);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8395)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8458 =
        bind get
          (fun ps  ->
             let uu____8468 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8468 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8505  ->
                       let uu____8506 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8506);
                  bind dismiss_all
                    (fun uu____8509  ->
                       let uu____8510 =
                         let uu____8517 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8517
                           keepGoing gt1
                          in
                       bind uu____8510
                         (fun uu____8529  ->
                            match uu____8529 with
                            | (gt',uu____8537) ->
                                (log ps
                                   (fun uu____8541  ->
                                      let uu____8542 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8542);
                                 (let uu____8543 = push_goals gs  in
                                  bind uu____8543
                                    (fun uu____8548  ->
                                       let uu____8549 =
                                         let uu____8552 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8552]  in
                                       add_goals uu____8549)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8458
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8575 =
        bind get
          (fun ps  ->
             let uu____8585 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8585 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8622  ->
                       let uu____8623 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8623);
                  bind dismiss_all
                    (fun uu____8626  ->
                       let uu____8627 =
                         let uu____8630 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8630 gt1
                          in
                       bind uu____8627
                         (fun gt'  ->
                            log ps
                              (fun uu____8638  ->
                                 let uu____8639 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8639);
                            (let uu____8640 = push_goals gs  in
                             bind uu____8640
                               (fun uu____8645  ->
                                  let uu____8646 =
                                    let uu____8649 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8649]  in
                                  add_goals uu____8646))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8575
  
let (trefl : unit -> unit tac) =
  fun uu____8660  ->
    let uu____8663 =
      let uu____8666 = cur_goal ()  in
      bind uu____8666
        (fun g  ->
           let uu____8684 =
             let uu____8689 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8689  in
           match uu____8684 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8697 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8697 with
                | (hd1,args) ->
                    let uu____8730 =
                      let uu____8741 =
                        let uu____8742 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8742.FStar_Syntax_Syntax.n  in
                      (uu____8741, args)  in
                    (match uu____8730 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8754::(l,uu____8756)::(r,uu____8758)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8785 =
                           let uu____8788 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8788 l r  in
                         bind uu____8785
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8795 =
                                  let uu____8796 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8796 l  in
                                let uu____8797 =
                                  let uu____8798 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8798 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8795 uu____8797
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8801) ->
                         let uu____8814 =
                           let uu____8815 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8815 t  in
                         fail1 "trefl: not an equality (%s)" uu____8814))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8663
  
let (dup : unit -> unit tac) =
  fun uu____8828  ->
    let uu____8831 = cur_goal ()  in
    bind uu____8831
      (fun g  ->
         let uu____8837 =
           let uu____8844 = FStar_Tactics_Types.goal_env g  in
           let uu____8845 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8844 uu____8845  in
         bind uu____8837
           (fun uu____8854  ->
              match uu____8854 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___396_8864 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___396_8864.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___396_8864.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___396_8864.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8867  ->
                       let uu____8868 =
                         let uu____8871 = FStar_Tactics_Types.goal_env g  in
                         let uu____8872 =
                           let uu____8873 =
                             let uu____8874 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8875 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8874
                               uu____8875
                              in
                           let uu____8876 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8877 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8873 uu____8876 u
                             uu____8877
                            in
                         add_irrelevant_goal "dup equation" uu____8871
                           uu____8872 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8868
                         (fun uu____8880  ->
                            let uu____8881 = add_goals [g']  in
                            bind uu____8881 (fun uu____8885  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8892  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___397_8909 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___397_8909.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___397_8909.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___397_8909.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___397_8909.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___397_8909.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___397_8909.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___397_8909.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___397_8909.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___397_8909.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___397_8909.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___397_8909.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____8910 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8919  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___398_8932 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___398_8932.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___398_8932.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___398_8932.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___398_8932.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___398_8932.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___398_8932.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___398_8932.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___398_8932.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___398_8932.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___398_8932.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___398_8932.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8939  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8946 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8966 =
      let uu____8973 = cur_goal ()  in
      bind uu____8973
        (fun g  ->
           let uu____8983 =
             let uu____8992 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8992 t  in
           bind uu____8983
             (fun uu____9020  ->
                match uu____9020 with
                | (t1,typ,guard) ->
                    let uu____9036 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9036 with
                     | (hd1,args) ->
                         let uu____9079 =
                           let uu____9092 =
                             let uu____9093 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9093.FStar_Syntax_Syntax.n  in
                           (uu____9092, args)  in
                         (match uu____9079 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9112)::(q,uu____9114)::[]) when
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
                                let uu____9152 =
                                  let uu____9153 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9153
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9152
                                 in
                              let g2 =
                                let uu____9155 =
                                  let uu____9156 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9156
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9155
                                 in
                              bind __dismiss
                                (fun uu____9163  ->
                                   let uu____9164 = add_goals [g1; g2]  in
                                   bind uu____9164
                                     (fun uu____9173  ->
                                        let uu____9174 =
                                          let uu____9179 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9180 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9179, uu____9180)  in
                                        ret uu____9174))
                          | uu____9185 ->
                              let uu____9198 =
                                let uu____9199 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9199 typ  in
                              fail1 "Not a disjunction: %s" uu____9198))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8966
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9229 =
      let uu____9232 = cur_goal ()  in
      bind uu____9232
        (fun g  ->
           FStar_Options.push ();
           (let uu____9245 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9245);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___399_9252 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___399_9252.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___399_9252.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___399_9252.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9229
  
let (top_env : unit -> env tac) =
  fun uu____9264  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9277  ->
    let uu____9280 = cur_goal ()  in
    bind uu____9280
      (fun g  ->
         let uu____9286 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9286)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9295  ->
    let uu____9298 = cur_goal ()  in
    bind uu____9298
      (fun g  ->
         let uu____9304 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9304)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9313  ->
    let uu____9316 = cur_goal ()  in
    bind uu____9316
      (fun g  ->
         let uu____9322 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9322)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9339 =
        mlog
          (fun uu____9344  ->
             let uu____9345 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9345)
          (fun uu____9348  ->
             let uu____9349 = cur_goal ()  in
             bind uu____9349
               (fun goal  ->
                  let env =
                    let uu____9357 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9357 ty  in
                  let uu____9358 = __tc env tm  in
                  bind uu____9358
                    (fun uu____9377  ->
                       match uu____9377 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9391  ->
                                let uu____9392 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9392)
                             (fun uu____9394  ->
                                mlog
                                  (fun uu____9397  ->
                                     let uu____9398 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9398)
                                  (fun uu____9401  ->
                                     let uu____9402 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9402
                                       (fun uu____9406  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9339
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9429 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9435 =
              let uu____9442 =
                let uu____9443 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9443
                 in
              new_uvar "uvar_env.2" env uu____9442  in
            bind uu____9435
              (fun uu____9459  ->
                 match uu____9459 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9429
        (fun typ  ->
           let uu____9471 = new_uvar "uvar_env" env typ  in
           bind uu____9471
             (fun uu____9485  -> match uu____9485 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9503 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9522 -> g.FStar_Tactics_Types.opts
             | uu____9525 -> FStar_Options.peek ()  in
           let uu____9528 = FStar_Syntax_Util.head_and_args t  in
           match uu____9528 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9546);
                FStar_Syntax_Syntax.pos = uu____9547;
                FStar_Syntax_Syntax.vars = uu____9548;_},uu____9549)
               ->
               let env1 =
                 let uu___400_9587 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___400_9587.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___400_9587.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___400_9587.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___400_9587.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___400_9587.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___400_9587.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___400_9587.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___400_9587.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___400_9587.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___400_9587.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___400_9587.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___400_9587.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___400_9587.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___400_9587.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___400_9587.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___400_9587.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___400_9587.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___400_9587.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___400_9587.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___400_9587.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___400_9587.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___400_9587.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___400_9587.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___400_9587.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___400_9587.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___400_9587.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___400_9587.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___400_9587.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___400_9587.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___400_9587.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___400_9587.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___400_9587.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___400_9587.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___400_9587.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___400_9587.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___400_9587.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___400_9587.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___400_9587.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___400_9587.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___400_9587.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9589 =
                 let uu____9592 = bnorm_goal g  in [uu____9592]  in
               add_goals uu____9589
           | uu____9593 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9503
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9640 = if b then t2 else ret false  in
             bind uu____9640 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9651 = trytac comp  in
      bind uu____9651
        (fun uu___342_9659  ->
           match uu___342_9659 with
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
        let uu____9685 =
          bind get
            (fun ps  ->
               let uu____9691 = __tc e t1  in
               bind uu____9691
                 (fun uu____9711  ->
                    match uu____9711 with
                    | (t11,ty1,g1) ->
                        let uu____9723 = __tc e t2  in
                        bind uu____9723
                          (fun uu____9743  ->
                             match uu____9743 with
                             | (t21,ty2,g2) ->
                                 let uu____9755 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____9755
                                   (fun uu____9760  ->
                                      let uu____9761 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____9761
                                        (fun uu____9767  ->
                                           let uu____9768 =
                                             do_unify e ty1 ty2  in
                                           let uu____9771 =
                                             do_unify e t11 t21  in
                                           tac_and uu____9768 uu____9771)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9685
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9804  ->
             let uu____9805 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9805
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
        (fun uu____9826  ->
           let uu____9827 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9827)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9837 =
      mlog
        (fun uu____9842  ->
           let uu____9843 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9843)
        (fun uu____9846  ->
           let uu____9847 = cur_goal ()  in
           bind uu____9847
             (fun g  ->
                let uu____9853 =
                  let uu____9862 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9862 ty  in
                bind uu____9853
                  (fun uu____9874  ->
                     match uu____9874 with
                     | (ty1,uu____9884,guard) ->
                         let uu____9886 =
                           let uu____9889 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9889 guard  in
                         bind uu____9886
                           (fun uu____9892  ->
                              let uu____9893 =
                                let uu____9896 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9897 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9896 uu____9897 ty1  in
                              bind uu____9893
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9903 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9903
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
                                        let uu____9909 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9910 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9909 uu____9910
                                         in
                                      let nty =
                                        let uu____9912 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9912 ty1  in
                                      let uu____9913 =
                                        let uu____9916 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9916 ng nty  in
                                      bind uu____9913
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9922 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9922
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9837
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9944::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9972 = init xs  in x :: uu____9972
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9984 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9992) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10049 = last args  in
          (match uu____10049 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10071 =
                 let uu____10072 =
                   let uu____10077 =
                     let uu____10078 =
                       let uu____10083 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10083  in
                     uu____10078 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10077, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10072  in
               FStar_All.pipe_left ret uu____10071)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10094,uu____10095) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10139 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10139 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10172 =
                      let uu____10173 =
                        let uu____10178 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10178)  in
                      FStar_Reflection_Data.Tv_Abs uu____10173  in
                    FStar_All.pipe_left ret uu____10172))
      | FStar_Syntax_Syntax.Tm_type uu____10181 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10201 ->
          let uu____10214 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10214 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10244 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10244 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10283 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10291 =
            let uu____10292 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10292  in
          FStar_All.pipe_left ret uu____10291
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10313 =
            let uu____10314 =
              let uu____10319 =
                let uu____10320 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10320  in
              (uu____10319, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10314  in
          FStar_All.pipe_left ret uu____10313
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10354 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10359 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10359 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10398 ->
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
             | FStar_Util.Inr uu____10428 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10432 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10432 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10452 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10456 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10510 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10510
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10529 =
                  let uu____10536 =
                    FStar_List.map
                      (fun uu____10548  ->
                         match uu____10548 with
                         | (p1,uu____10556) -> inspect_pat p1) ps
                     in
                  (fv, uu____10536)  in
                FStar_Reflection_Data.Pat_Cons uu____10529
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
              (fun uu___343_10650  ->
                 match uu___343_10650 with
                 | (pat,uu____10672,t4) ->
                     let uu____10690 = inspect_pat pat  in (uu____10690, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10699 ->
          ((let uu____10701 =
              let uu____10706 =
                let uu____10707 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10708 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10707 uu____10708
                 in
              (FStar_Errors.Warning_CantInspect, uu____10706)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10701);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9984
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10721 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10721
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10725 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10725
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10729 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10729
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10736 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10736
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10755 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10755
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10768 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10768
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10783 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10783
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10787 =
          let uu____10788 =
            let uu____10795 =
              let uu____10796 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10796  in
            FStar_Syntax_Syntax.mk uu____10795  in
          uu____10788 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10787
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10804 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10804
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10813 =
          let uu____10814 =
            let uu____10821 =
              let uu____10822 =
                let uu____10835 =
                  let uu____10838 =
                    let uu____10839 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10839]  in
                  FStar_Syntax_Subst.close uu____10838 t2  in
                ((false, [lb]), uu____10835)  in
              FStar_Syntax_Syntax.Tm_let uu____10822  in
            FStar_Syntax_Syntax.mk uu____10821  in
          uu____10814 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10813
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10873 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10873 with
         | (lbs,body) ->
             let uu____10888 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10888)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10922 =
                let uu____10923 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10923  in
              FStar_All.pipe_left wrap uu____10922
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10930 =
                let uu____10931 =
                  let uu____10944 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10960 = pack_pat p1  in
                         (uu____10960, false)) ps
                     in
                  (fv, uu____10944)  in
                FStar_Syntax_Syntax.Pat_cons uu____10931  in
              FStar_All.pipe_left wrap uu____10930
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
            (fun uu___344_11006  ->
               match uu___344_11006 with
               | (pat,t1) ->
                   let uu____11023 = pack_pat pat  in
                   (uu____11023, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11071 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11071
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11099 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11099
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11145 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11145
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11184 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11184
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11205 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11205 with
      | (u,ctx_uvars,g_u) ->
          let uu____11237 = FStar_List.hd ctx_uvars  in
          (match uu____11237 with
           | (ctx_uvar,uu____11251) ->
               let g =
                 let uu____11253 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11253 false
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
        let uu____11273 = goal_of_goal_ty env typ  in
        match uu____11273 with
        | (g,g_u) ->
            let ps =
              let uu____11285 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11285
              }  in
            let uu____11290 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11290)
  