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
      try t.tac_f p
      with
      | FStar_Errors.Err (uu____163,msg) ->
          FStar_Tactics_Result.Failed (msg, p)
      | FStar_Errors.Error (uu____165,msg,uu____167) ->
          FStar_Tactics_Result.Failed (msg, p)
      | e ->
          let uu____169 =
            let uu____174 = FStar_Util.message_of_exn e  in (uu____174, p)
             in
          FStar_Tactics_Result.Failed uu____169
  
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
           let uu____246 = run t1 p  in
           match uu____246 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____253 = t2 a  in run uu____253 q
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
    let uu____273 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____273 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____291 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____292 =
      let uu____293 = check_goal_solved g  in
      match uu____293 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____297 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____297
       in
    FStar_Util.format2 "%s%s" uu____291 uu____292
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____308 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____308
      then goal_to_string_verbose g
      else
        (let w =
           let uu____311 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____311 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____315 = FStar_Tactics_Types.goal_env g  in
               tts uu____315 t
            in
         let uu____316 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____317 =
           let uu____318 = FStar_Tactics_Types.goal_env g  in
           tts uu____318
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____316 w uu____317)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____334 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____334
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____350 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____350
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____371 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____371
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____378) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____388) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____403 =
      let uu____408 =
        let uu____409 = FStar_Tactics_Types.goal_env g  in
        let uu____410 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____409 uu____410  in
      FStar_Syntax_Util.un_squash uu____408  in
    match uu____403 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____416 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____444 =
            let uu____445 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____445  in
          if uu____444 then tacprint msg else ());
         ret ())
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____458 = goal_to_string ps goal  in tacprint uu____458
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____470 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____474 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____474))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____483  ->
    match uu____483 with
    | (msg,ps) ->
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____496 =
          let uu____499 =
            let uu____500 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____500 msg
             in
          let uu____501 =
            let uu____504 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____505 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____505
              else ""  in
            let uu____507 =
              let uu____510 =
                let uu____511 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____511
                then
                  let uu____512 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____512
                else ""  in
              let uu____514 =
                let uu____517 =
                  let uu____518 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____519 =
                    let uu____520 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____520  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____518
                    uu____519
                   in
                let uu____523 =
                  let uu____526 =
                    let uu____527 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____528 =
                      let uu____529 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____529  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____527
                      uu____528
                     in
                  [uu____526]  in
                uu____517 :: uu____523  in
              uu____510 :: uu____514  in
            uu____504 :: uu____507  in
          uu____499 :: uu____501  in
        FStar_String.concat "" uu____496
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____538 =
        let uu____539 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____539  in
      let uu____540 =
        let uu____545 =
          let uu____546 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____546  in
        FStar_Syntax_Print.binders_to_json uu____545  in
      FStar_All.pipe_right uu____538 uu____540  in
    let uu____547 =
      let uu____554 =
        let uu____561 =
          let uu____566 =
            let uu____567 =
              let uu____574 =
                let uu____579 =
                  let uu____580 =
                    let uu____581 = FStar_Tactics_Types.goal_env g  in
                    let uu____582 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____581 uu____582  in
                  FStar_Util.JsonStr uu____580  in
                ("witness", uu____579)  in
              let uu____583 =
                let uu____590 =
                  let uu____595 =
                    let uu____596 =
                      let uu____597 = FStar_Tactics_Types.goal_env g  in
                      let uu____598 = FStar_Tactics_Types.goal_type g  in
                      tts uu____597 uu____598  in
                    FStar_Util.JsonStr uu____596  in
                  ("type", uu____595)  in
                [uu____590]  in
              uu____574 :: uu____583  in
            FStar_Util.JsonAssoc uu____567  in
          ("goal", uu____566)  in
        [uu____561]  in
      ("hyps", g_binders) :: uu____554  in
    FStar_Util.JsonAssoc uu____547
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____631  ->
    match uu____631 with
    | (msg,ps) ->
        let uu____638 =
          let uu____645 =
            let uu____652 =
              let uu____659 =
                let uu____666 =
                  let uu____671 =
                    let uu____672 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____672  in
                  ("goals", uu____671)  in
                let uu____675 =
                  let uu____682 =
                    let uu____687 =
                      let uu____688 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____688  in
                    ("smt-goals", uu____687)  in
                  [uu____682]  in
                uu____666 :: uu____675  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____659
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____652  in
          let uu____711 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____724 =
                let uu____729 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____729)  in
              [uu____724]
            else []  in
          FStar_List.append uu____645 uu____711  in
        FStar_Util.JsonAssoc uu____638
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____759  ->
           FStar_Options.set_option "print_effect_args"
             (FStar_Options.Bool true);
           FStar_Util.print_generic "proof-state" ps_to_string ps_to_json
             (msg, ps))
  
let (print_proof_state1 : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____782 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____782 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____800 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____800 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____854 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____854
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____862 . Prims.string -> Prims.string -> 'Auu____862 tac =
  fun msg  ->
    fun x  -> let uu____875 = FStar_Util.format1 msg x  in fail uu____875
  
let fail2 :
  'Auu____884 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____884 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____902 = FStar_Util.format2 msg x y  in fail uu____902
  
let fail3 :
  'Auu____913 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____913 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____936 = FStar_Util.format3 msg x y z  in fail uu____936
  
let fail4 :
  'Auu____949 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____949 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____977 = FStar_Util.format4 msg x y z w  in fail uu____977
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1010 = run t ps  in
         match uu____1010 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___356_1034 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___356_1034.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___356_1034.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___356_1034.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___356_1034.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___356_1034.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___356_1034.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___356_1034.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___356_1034.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___356_1034.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___356_1034.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___356_1034.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1061 = trytac' t  in
    bind uu____1061
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1088 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1124 = trytac t  in run uu____1124 ps
         with
         | FStar_Errors.Err (uu____1140,msg) ->
             (log ps
                (fun uu____1144  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1149,msg,uu____1151) ->
             (log ps
                (fun uu____1154  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1187 = run t ps  in
           match uu____1187 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1206  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1227 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1227
         then
           let uu____1228 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1229 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1228
             uu____1229
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1241 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1241
            then
              let uu____1242 = FStar_Util.string_of_bool res  in
              let uu____1243 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1244 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1242 uu____1243 uu____1244
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1252,msg) ->
             mlog
               (fun uu____1255  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1257  -> ret false)
         | FStar_Errors.Error (uu____1258,msg,r) ->
             mlog
               (fun uu____1263  ->
                  let uu____1264 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1264) (fun uu____1266  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___361_1277 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___361_1277.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___361_1277.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___361_1277.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___362_1280 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___362_1280.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___362_1280.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___362_1280.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___362_1280.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___362_1280.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___362_1280.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___362_1280.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___362_1280.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___362_1280.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___362_1280.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___362_1280.FStar_Tactics_Types.tac_verb_dbg)
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
          (fun uu____1303  ->
             (let uu____1305 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1305
              then
                (FStar_Options.push ();
                 (let uu____1307 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1309 = __do_unify env t1 t2  in
              bind uu____1309
                (fun r  ->
                   (let uu____1316 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1316 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1319  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___363_1326 = ps  in
         let uu____1327 =
           FStar_List.filter
             (fun g  ->
                let uu____1333 = check_goal_solved g  in
                FStar_Option.isNone uu____1333) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___363_1326.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___363_1326.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___363_1326.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1327;
           FStar_Tactics_Types.smt_goals =
             (uu___363_1326.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___363_1326.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___363_1326.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___363_1326.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___363_1326.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___363_1326.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___363_1326.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___363_1326.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1350 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1350 with
      | FStar_Pervasives_Native.Some uu____1355 ->
          let uu____1356 =
            let uu____1357 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1357  in
          fail uu____1356
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1373 = FStar_Tactics_Types.goal_env goal  in
      let uu____1374 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1373 solution uu____1374
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1380 =
         let uu___364_1381 = p  in
         let uu____1382 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_1381.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___364_1381.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___364_1381.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1382;
           FStar_Tactics_Types.smt_goals =
             (uu___364_1381.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_1381.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_1381.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_1381.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_1381.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_1381.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_1381.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_1381.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1380)
  
let (dismiss : unit -> unit tac) =
  fun uu____1391  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1398 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1419  ->
           let uu____1420 =
             let uu____1421 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1421  in
           let uu____1422 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1420 uu____1422)
        (fun uu____1425  ->
           let uu____1426 = trysolve goal solution  in
           bind uu____1426
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1434  -> remove_solved_goals)
                else
                  (let uu____1436 =
                     let uu____1437 =
                       let uu____1438 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1438 solution  in
                     let uu____1439 =
                       let uu____1440 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1441 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1440 uu____1441  in
                     let uu____1442 =
                       let uu____1443 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1444 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1443 uu____1444  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1437 uu____1439 uu____1442
                      in
                   fail uu____1436)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1459 = set_solution goal solution  in
      bind uu____1459
        (fun uu____1463  ->
           bind __dismiss (fun uu____1465  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___365_1472 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___365_1472.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___365_1472.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___365_1472.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___365_1472.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___365_1472.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___365_1472.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___365_1472.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___365_1472.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___365_1472.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___365_1472.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___365_1472.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1491 = FStar_Options.defensive ()  in
    if uu____1491
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1496 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1496)
         in
      let b2 =
        b1 &&
          (let uu____1499 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1499)
         in
      let rec aux b3 e =
        let uu____1511 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1511 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1529 =
        (let uu____1532 = aux b2 env  in Prims.op_Negation uu____1532) &&
          (let uu____1534 = FStar_ST.op_Bang nwarn  in
           uu____1534 < (Prims.parse_int "5"))
         in
      (if uu____1529
       then
         ((let uu____1555 =
             let uu____1556 = FStar_Tactics_Types.goal_type g  in
             uu____1556.FStar_Syntax_Syntax.pos  in
           let uu____1559 =
             let uu____1564 =
               let uu____1565 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1565
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1564)  in
           FStar_Errors.log_issue uu____1555 uu____1559);
          (let uu____1566 =
             let uu____1567 = FStar_ST.op_Bang nwarn  in
             uu____1567 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1566))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___366_1627 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___366_1627.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___366_1627.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___366_1627.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___366_1627.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___366_1627.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___366_1627.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___366_1627.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___366_1627.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___366_1627.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___366_1627.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___366_1627.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___367_1647 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_1647.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_1647.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_1647.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___367_1647.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___367_1647.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_1647.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_1647.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_1647.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_1647.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_1647.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_1647.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___368_1667 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1667.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1667.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1667.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___368_1667.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_1667.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1667.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1667.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1667.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___368_1667.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___368_1667.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_1667.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1687 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1687.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1687.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1687.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___369_1687.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___369_1687.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1687.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1687.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1687.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1687.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1687.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1687.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1698  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___370_1712 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1712.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1712.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_1712.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___370_1712.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_1712.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1712.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1712.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1712.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1712.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1712.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1712.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1740 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1740 with
        | (u,ctx_uvar,g_u) ->
            let uu____1774 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1774
              (fun uu____1783  ->
                 let uu____1784 =
                   let uu____1789 =
                     let uu____1790 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1790  in
                   (u, uu____1789)  in
                 ret uu____1784)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1808 = FStar_Syntax_Util.un_squash t  in
    match uu____1808 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1818 =
          let uu____1819 = FStar_Syntax_Subst.compress t'  in
          uu____1819.FStar_Syntax_Syntax.n  in
        (match uu____1818 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1823 -> false)
    | uu____1824 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1834 = FStar_Syntax_Util.un_squash t  in
    match uu____1834 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1844 =
          let uu____1845 = FStar_Syntax_Subst.compress t'  in
          uu____1845.FStar_Syntax_Syntax.n  in
        (match uu____1844 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1849 -> false)
    | uu____1850 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1861  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1872 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1872 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1879 = goal_to_string_verbose hd1  in
                    let uu____1880 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1879 uu____1880);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1887  ->
    let uu____1890 =
      bind get
        (fun ps  ->
           let uu____1896 = cur_goal ()  in
           bind uu____1896
             (fun g  ->
                (let uu____1903 =
                   let uu____1904 = FStar_Tactics_Types.goal_type g  in
                   uu____1904.FStar_Syntax_Syntax.pos  in
                 let uu____1907 =
                   let uu____1912 =
                     let uu____1913 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1913
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1912)  in
                 FStar_Errors.log_issue uu____1903 uu____1907);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1890
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1924  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___371_1934 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___371_1934.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___371_1934.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___371_1934.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___371_1934.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___371_1934.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___371_1934.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___371_1934.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___371_1934.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___371_1934.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___371_1934.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___371_1934.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1935 = set ps1  in
         bind uu____1935
           (fun uu____1940  ->
              let uu____1941 = FStar_BigInt.of_int_fs n1  in ret uu____1941))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1948  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1956 = FStar_BigInt.of_int_fs n1  in ret uu____1956)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1969  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1977 = FStar_BigInt.of_int_fs n1  in ret uu____1977)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1990  ->
    let uu____1993 = cur_goal ()  in
    bind uu____1993 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2025 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2025 phi  in
          let uu____2026 = new_uvar reason env typ  in
          bind uu____2026
            (fun uu____2041  ->
               match uu____2041 with
               | (uu____2048,ctx_uvar) ->
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
             (fun uu____2093  ->
                let uu____2094 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2094)
             (fun uu____2097  ->
                let e1 =
                  let uu___372_2099 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___372_2099.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___372_2099.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___372_2099.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___372_2099.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___372_2099.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___372_2099.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___372_2099.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___372_2099.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___372_2099.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___372_2099.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___372_2099.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___372_2099.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___372_2099.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___372_2099.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___372_2099.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___372_2099.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___372_2099.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___372_2099.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___372_2099.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___372_2099.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___372_2099.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___372_2099.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___372_2099.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___372_2099.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___372_2099.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___372_2099.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___372_2099.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___372_2099.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___372_2099.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___372_2099.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___372_2099.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___372_2099.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___372_2099.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___372_2099.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___372_2099.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___372_2099.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___372_2099.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___372_2099.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___372_2099.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___372_2099.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___372_2099.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  let uu____2119 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2119
                with
                | FStar_Errors.Err (uu____2146,msg) ->
                    let uu____2148 = tts e1 t  in
                    let uu____2149 =
                      let uu____2150 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2150
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2148 uu____2149 msg
                | FStar_Errors.Error (uu____2157,msg,uu____2159) ->
                    let uu____2160 = tts e1 t  in
                    let uu____2161 =
                      let uu____2162 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2162
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2160 uu____2161 msg))
  
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
  fun uu____2189  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___375_2207 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___375_2207.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___375_2207.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___375_2207.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___375_2207.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___375_2207.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___375_2207.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___375_2207.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___375_2207.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___375_2207.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___375_2207.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___375_2207.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2231 = get_guard_policy ()  in
      bind uu____2231
        (fun old_pol  ->
           let uu____2237 = set_guard_policy pol  in
           bind uu____2237
             (fun uu____2241  ->
                bind t
                  (fun r  ->
                     let uu____2245 = set_guard_policy old_pol  in
                     bind uu____2245 (fun uu____2249  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2252 = let uu____2257 = cur_goal ()  in trytac uu____2257  in
  bind uu____2252
    (fun uu___346_2264  ->
       match uu___346_2264 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2270 = FStar_Options.peek ()  in ret uu____2270)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2293 =
               let uu____2294 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2294.FStar_TypeChecker_Env.guard_f  in
             match uu____2293 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2298 = istrivial e f  in
                 if uu____2298
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2306 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2306
                              (fun goal  ->
                                 let goal1 =
                                   let uu___376_2313 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___376_2313.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___376_2313.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___376_2313.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2314 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2314
                              (fun goal  ->
                                 let goal1 =
                                   let uu___377_2321 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___377_2321.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___377_2321.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___377_2321.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2329 =
                                 let uu____2330 =
                                   let uu____2331 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2331
                                    in
                                 Prims.op_Negation uu____2330  in
                               if uu____2329
                               then
                                 mlog
                                   (fun uu____2336  ->
                                      let uu____2337 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2337)
                                   (fun uu____2339  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2346 ->
                                 mlog
                                   (fun uu____2349  ->
                                      let uu____2350 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2350)
                                   (fun uu____2352  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2362 =
      let uu____2365 = cur_goal ()  in
      bind uu____2365
        (fun goal  ->
           let uu____2371 =
             let uu____2380 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2380 t  in
           bind uu____2371
             (fun uu____2391  ->
                match uu____2391 with
                | (uu____2400,typ,uu____2402) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2362
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2431 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2431 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2442  ->
    let uu____2445 = cur_goal ()  in
    bind uu____2445
      (fun goal  ->
         let uu____2451 =
           let uu____2452 = FStar_Tactics_Types.goal_env goal  in
           let uu____2453 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2452 uu____2453  in
         if uu____2451
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2457 =
              let uu____2458 = FStar_Tactics_Types.goal_env goal  in
              let uu____2459 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2458 uu____2459  in
            fail1 "Not a trivial goal: %s" uu____2457))
  
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
          let uu____2488 =
            let uu____2489 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2489.FStar_TypeChecker_Env.guard_f  in
          match uu____2488 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2497 = istrivial e f  in
              if uu____2497
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2505 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2505
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___380_2515 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___380_2515.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___380_2515.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___380_2515.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2522  ->
    let uu____2525 = cur_goal ()  in
    bind uu____2525
      (fun g  ->
         let uu____2531 = is_irrelevant g  in
         if uu____2531
         then bind __dismiss (fun uu____2535  -> add_smt_goals [g])
         else
           (let uu____2537 =
              let uu____2538 = FStar_Tactics_Types.goal_env g  in
              let uu____2539 = FStar_Tactics_Types.goal_type g  in
              tts uu____2538 uu____2539  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2537))
  
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
             let uu____2588 =
               try
                 let uu____2622 =
                   let uu____2631 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2631 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2622
               with | uu____2653 -> fail "divide: not enough goals"  in
             bind uu____2588
               (fun uu____2679  ->
                  match uu____2679 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___381_2705 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___381_2705.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___381_2705.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___381_2705.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___381_2705.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___381_2705.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___381_2705.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___381_2705.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___381_2705.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___381_2705.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___381_2705.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2706 = set lp  in
                      bind uu____2706
                        (fun uu____2714  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___382_2730 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___382_2730.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___382_2730.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___382_2730.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___382_2730.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___382_2730.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___382_2730.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___382_2730.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___382_2730.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___382_2730.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___382_2730.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2731 = set rp  in
                                     bind uu____2731
                                       (fun uu____2739  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___383_2755 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___383_2755.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___383_2755.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2756 = set p'
                                                       in
                                                    bind uu____2756
                                                      (fun uu____2764  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2770 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2791 = divide FStar_BigInt.one f idtac  in
    bind uu____2791
      (fun uu____2804  -> match uu____2804 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2841::uu____2842 ->
             let uu____2845 =
               let uu____2854 = map tau  in
               divide FStar_BigInt.one tau uu____2854  in
             bind uu____2845
               (fun uu____2872  ->
                  match uu____2872 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2913 =
        bind t1
          (fun uu____2918  ->
             let uu____2919 = map t2  in
             bind uu____2919 (fun uu____2927  -> ret ()))
         in
      focus uu____2913
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2936  ->
    let uu____2939 =
      let uu____2942 = cur_goal ()  in
      bind uu____2942
        (fun goal  ->
           let uu____2951 =
             let uu____2958 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2958  in
           match uu____2951 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2967 =
                 let uu____2968 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2968  in
               if uu____2967
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2973 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2973 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2987 = new_uvar "intro" env' typ'  in
                  bind uu____2987
                    (fun uu____3003  ->
                       match uu____3003 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3027 = set_solution goal sol  in
                           bind uu____3027
                             (fun uu____3033  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3035 =
                                  let uu____3038 = bnorm_goal g  in
                                  replace_cur uu____3038  in
                                bind uu____3035 (fun uu____3040  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3045 =
                 let uu____3046 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3047 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3046 uu____3047  in
               fail1 "goal is not an arrow (%s)" uu____3045)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2939
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3062  ->
    let uu____3069 = cur_goal ()  in
    bind uu____3069
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3086 =
            let uu____3093 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3093  in
          match uu____3086 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3106 =
                let uu____3107 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3107  in
              if uu____3106
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3120 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3120
                    in
                 let bs =
                   let uu____3130 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3130; b]  in
                 let env' =
                   let uu____3156 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3156 bs  in
                 let uu____3157 =
                   let uu____3164 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3164  in
                 bind uu____3157
                   (fun uu____3183  ->
                      match uu____3183 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3197 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3200 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3197
                              FStar_Parser_Const.effect_Tot_lid uu____3200 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3218 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3218 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3240 =
                                   let uu____3241 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3241.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3240
                                  in
                               let uu____3254 = set_solution goal tm  in
                               bind uu____3254
                                 (fun uu____3263  ->
                                    let uu____3264 =
                                      let uu____3267 =
                                        bnorm_goal
                                          (let uu___386_3270 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___386_3270.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___386_3270.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___386_3270.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3267  in
                                    bind uu____3264
                                      (fun uu____3277  ->
                                         let uu____3278 =
                                           let uu____3283 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3283, b)  in
                                         ret uu____3278)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3292 =
                let uu____3293 = FStar_Tactics_Types.goal_env goal  in
                let uu____3294 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3293 uu____3294  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3292))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3312 = cur_goal ()  in
    bind uu____3312
      (fun goal  ->
         mlog
           (fun uu____3319  ->
              let uu____3320 =
                let uu____3321 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3321  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3320)
           (fun uu____3326  ->
              let steps =
                let uu____3330 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3330
                 in
              let t =
                let uu____3334 = FStar_Tactics_Types.goal_env goal  in
                let uu____3335 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3334 uu____3335  in
              let uu____3336 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3336))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3360 =
          mlog
            (fun uu____3365  ->
               let uu____3366 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3366)
            (fun uu____3368  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3374 -> g.FStar_Tactics_Types.opts
                      | uu____3377 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3382  ->
                         let uu____3383 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3383)
                      (fun uu____3386  ->
                         let uu____3387 = __tc e t  in
                         bind uu____3387
                           (fun uu____3408  ->
                              match uu____3408 with
                              | (t1,uu____3418,uu____3419) ->
                                  let steps =
                                    let uu____3423 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3423
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3360
  
let (refine_intro : unit -> unit tac) =
  fun uu____3437  ->
    let uu____3440 =
      let uu____3443 = cur_goal ()  in
      bind uu____3443
        (fun g  ->
           let uu____3450 =
             let uu____3461 = FStar_Tactics_Types.goal_env g  in
             let uu____3462 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3461 uu____3462
              in
           match uu____3450 with
           | (uu____3465,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3490 =
                 let uu____3495 =
                   let uu____3500 =
                     let uu____3501 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3501]  in
                   FStar_Syntax_Subst.open_term uu____3500 phi  in
                 match uu____3495 with
                 | (bvs,phi1) ->
                     let uu____3526 =
                       let uu____3527 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3527  in
                     (uu____3526, phi1)
                  in
               (match uu____3490 with
                | (bv1,phi1) ->
                    let uu____3546 =
                      let uu____3549 = FStar_Tactics_Types.goal_env g  in
                      let uu____3550 =
                        let uu____3551 =
                          let uu____3554 =
                            let uu____3555 =
                              let uu____3562 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3562)  in
                            FStar_Syntax_Syntax.NT uu____3555  in
                          [uu____3554]  in
                        FStar_Syntax_Subst.subst uu____3551 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3549
                        uu____3550 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3546
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3570  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3440
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3589 = cur_goal ()  in
      bind uu____3589
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3597 = FStar_Tactics_Types.goal_env goal  in
               let uu____3598 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3597 uu____3598
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3600 = __tc env t  in
           bind uu____3600
             (fun uu____3619  ->
                match uu____3619 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3634  ->
                         let uu____3635 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3636 =
                           let uu____3637 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3637
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3635 uu____3636)
                      (fun uu____3640  ->
                         let uu____3641 =
                           let uu____3644 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3644 guard  in
                         bind uu____3641
                           (fun uu____3646  ->
                              mlog
                                (fun uu____3650  ->
                                   let uu____3651 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3652 =
                                     let uu____3653 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3653
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3651 uu____3652)
                                (fun uu____3656  ->
                                   let uu____3657 =
                                     let uu____3660 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3661 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3660 typ uu____3661  in
                                   bind uu____3657
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3667 =
                                             let uu____3668 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3668 t1  in
                                           let uu____3669 =
                                             let uu____3670 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3670 typ  in
                                           let uu____3671 =
                                             let uu____3672 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3673 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3672 uu____3673  in
                                           let uu____3674 =
                                             let uu____3675 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3676 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3675 uu____3676  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3667 uu____3669 uu____3671
                                             uu____3674)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3691 =
        mlog
          (fun uu____3696  ->
             let uu____3697 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3697)
          (fun uu____3700  ->
             let uu____3701 =
               let uu____3708 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3708  in
             bind uu____3701
               (fun uu___348_3717  ->
                  match uu___348_3717 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3727  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3730  ->
                           let uu____3731 =
                             let uu____3738 =
                               let uu____3741 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3741
                                 (fun uu____3746  ->
                                    let uu____3747 = refine_intro ()  in
                                    bind uu____3747
                                      (fun uu____3751  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3738  in
                           bind uu____3731
                             (fun uu___347_3758  ->
                                match uu___347_3758 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3766 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3691
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3816 = f x  in
          bind uu____3816
            (fun y  ->
               let uu____3824 = mapM f xs  in
               bind uu____3824 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3895 = do_unify e ty1 ty2  in
          bind uu____3895
            (fun uu___349_3907  ->
               if uu___349_3907
               then ret acc
               else
                 (let uu____3926 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3926 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3947 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3948 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3947
                        uu____3948
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3963 =
                        let uu____3964 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3964  in
                      if uu____3963
                      then fail "Codomain is effectful"
                      else
                        (let uu____3984 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3984
                           (fun uu____4010  ->
                              match uu____4010 with
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
      let uu____4096 =
        mlog
          (fun uu____4101  ->
             let uu____4102 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4102)
          (fun uu____4105  ->
             let uu____4106 = cur_goal ()  in
             bind uu____4106
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4114 = __tc e tm  in
                  bind uu____4114
                    (fun uu____4135  ->
                       match uu____4135 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4148 =
                             let uu____4159 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4159  in
                           bind uu____4148
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4202  ->
                                       fun w  ->
                                         match uu____4202 with
                                         | (uvt,q,uu____4220) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4252 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4269  ->
                                       fun s  ->
                                         match uu____4269 with
                                         | (uu____4281,uu____4282,uv) ->
                                             let uu____4284 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4284) uvs uu____4252
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4293 = solve' goal w  in
                                bind uu____4293
                                  (fun uu____4298  ->
                                     let uu____4299 =
                                       mapM
                                         (fun uu____4316  ->
                                            match uu____4316 with
                                            | (uvt,q,uv) ->
                                                let uu____4328 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4328 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4333 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4334 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4334
                                                     then ret ()
                                                     else
                                                       (let uu____4338 =
                                                          let uu____4341 =
                                                            bnorm_goal
                                                              (let uu___387_4344
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___387_4344.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___387_4344.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4341]  in
                                                        add_goals uu____4338)))
                                         uvs
                                        in
                                     bind uu____4299
                                       (fun uu____4348  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4096
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4373 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4373
    then
      let uu____4380 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4395 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4448 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4380 with
      | (pre,post) ->
          let post1 =
            let uu____4480 =
              let uu____4491 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4491]  in
            FStar_Syntax_Util.mk_app post uu____4480  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4521 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4521
       then
         let uu____4528 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4528
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4561 =
      let uu____4564 =
        bind get
          (fun ps  ->
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
                         let uu____4604 = FStar_Tactics_Types.goal_env goal
                            in
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
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4683 =
                                            FStar_List.fold_left
                                              (fun uu____4731  ->
                                                 fun uu____4732  ->
                                                   match (uu____4731,
                                                           uu____4732)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
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
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4883 =
                                                            let uu____4896 =
                                                              let uu____4897
                                                                =
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
                                                          match uu____4883
                                                          with
                                                          | (u,uu____4918,g_u)
                                                              ->
                                                              let uu____4932
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4932,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4683 with
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
                                                 do_unify uu____5014
                                                   uu____5015 uu____5016
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
                                                        tts uu____5025 tm1
                                                         in
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
                                                        tts uu____5027
                                                          uu____5028
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
                                                        tts uu____5030
                                                          uu____5031
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
                                                              (fun uu____5047
                                                                  ->
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
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5072
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
                                                                    let uu____5110
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5110)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5126
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5126
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5144)
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
                                                                 let uu____5188
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
                                                                    let uu____5218
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5218
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5240)
                                                                    ->
                                                                    let uu____5265
                                                                    =
                                                                    let uu____5266
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5266.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5265
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5274)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___388_5294
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___388_5294.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___388_5294.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___388_5294.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5297
                                                                    ->
                                                                    let env =
                                                                    let uu___389_5299
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___389_5299.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5301
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5301
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
                                                                    let uu____5304
                                                                    =
                                                                    let uu____5311
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5311
                                                                    term1  in
                                                                    match uu____5304
                                                                    with
                                                                    | 
                                                                    (uu____5312,uu____5313,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5315
                                                                    =
                                                                    let uu____5318
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5319
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5320
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5319
                                                                    uu____5320
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5322
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5318
                                                                    uu____5322
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5315
                                                                    (fun
                                                                    uu____5326
                                                                     ->
                                                                    ret []))))
                                                                    in
                                                                 bind
                                                                   uu____5188
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
                                                                    let uu____5388
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5388
                                                                    then
                                                                    let uu____5391
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5391
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
                                                                    let uu____5405
                                                                    =
                                                                    let uu____5406
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5406
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5405)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5407
                                                                    =
                                                                    let uu____5410
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5410
                                                                    guard  in
                                                                    bind
                                                                    uu____5407
                                                                    (fun
                                                                    uu____5413
                                                                     ->
                                                                    let uu____5414
                                                                    =
                                                                    let uu____5417
                                                                    =
                                                                    let uu____5418
                                                                    =
                                                                    let uu____5419
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5420
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5419
                                                                    uu____5420
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5418
                                                                     in
                                                                    if
                                                                    uu____5417
                                                                    then
                                                                    let uu____5423
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5423
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5414
                                                                    (fun
                                                                    uu____5426
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4564  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4561
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5448 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5448 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5458::(e1,uu____5460)::(e2,uu____5462)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5523 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5547 = destruct_eq' typ  in
    match uu____5547 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5577 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5577 with
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
        let uu____5639 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5639 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5687 = aux e'  in
               FStar_Util.map_opt uu____5687
                 (fun uu____5711  ->
                    match uu____5711 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5732 = aux e  in
      FStar_Util.map_opt uu____5732
        (fun uu____5756  ->
           match uu____5756 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5823 =
            let uu____5832 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5832  in
          FStar_Util.map_opt uu____5823
            (fun uu____5847  ->
               match uu____5847 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___390_5866 = bv  in
                     let uu____5867 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___390_5866.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___390_5866.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5867
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___391_5875 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5876 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5885 =
                       let uu____5888 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5888  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___391_5875.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5876;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5885;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___391_5875.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___391_5875.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___391_5875.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___392_5889 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___392_5889.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___392_5889.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___392_5889.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5899 =
      let uu____5902 = cur_goal ()  in
      bind uu____5902
        (fun goal  ->
           let uu____5910 = h  in
           match uu____5910 with
           | (bv,uu____5914) ->
               mlog
                 (fun uu____5922  ->
                    let uu____5923 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5924 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5923
                      uu____5924)
                 (fun uu____5927  ->
                    let uu____5928 =
                      let uu____5937 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5937  in
                    match uu____5928 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5958 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5958 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5973 =
                               let uu____5974 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5974.FStar_Syntax_Syntax.n  in
                             (match uu____5973 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___393_5991 = bv1  in
                                    let uu____5992 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___393_5991.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___393_5991.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5992
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___394_6000 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6001 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6010 =
                                      let uu____6013 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6013
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___394_6000.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6001;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6010;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___394_6000.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___394_6000.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___394_6000.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___395_6016 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___395_6016.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___395_6016.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___395_6016.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6017 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6018 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5899
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6043 =
        let uu____6046 = cur_goal ()  in
        bind uu____6046
          (fun goal  ->
             let uu____6057 = b  in
             match uu____6057 with
             | (bv,uu____6061) ->
                 let bv' =
                   let uu____6067 =
                     let uu___396_6068 = bv  in
                     let uu____6069 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6069;
                       FStar_Syntax_Syntax.index =
                         (uu___396_6068.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___396_6068.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6067  in
                 let s1 =
                   let uu____6073 =
                     let uu____6074 =
                       let uu____6081 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6081)  in
                     FStar_Syntax_Syntax.NT uu____6074  in
                   [uu____6073]  in
                 let uu____6086 = subst_goal bv bv' s1 goal  in
                 (match uu____6086 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6043
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6105 =
      let uu____6108 = cur_goal ()  in
      bind uu____6108
        (fun goal  ->
           let uu____6117 = b  in
           match uu____6117 with
           | (bv,uu____6121) ->
               let uu____6126 =
                 let uu____6135 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6135  in
               (match uu____6126 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6156 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6156 with
                     | (ty,u) ->
                         let uu____6165 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6165
                           (fun uu____6183  ->
                              match uu____6183 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___397_6193 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___397_6193.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___397_6193.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6197 =
                                      let uu____6198 =
                                        let uu____6205 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6205)  in
                                      FStar_Syntax_Syntax.NT uu____6198  in
                                    [uu____6197]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___398_6217 = b1  in
                                         let uu____6218 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___398_6217.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___398_6217.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6218
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6225  ->
                                       let new_goal =
                                         let uu____6227 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6228 =
                                           let uu____6229 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6229
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6227 uu____6228
                                          in
                                       let uu____6230 = add_goals [new_goal]
                                          in
                                       bind uu____6230
                                         (fun uu____6235  ->
                                            let uu____6236 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6236
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6105
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6259 =
        let uu____6262 = cur_goal ()  in
        bind uu____6262
          (fun goal  ->
             let uu____6271 = b  in
             match uu____6271 with
             | (bv,uu____6275) ->
                 let uu____6280 =
                   let uu____6289 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6289  in
                 (match uu____6280 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6313 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6313
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___399_6318 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___399_6318.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___399_6318.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6320 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6320))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6259
  
let (revert : unit -> unit tac) =
  fun uu____6331  ->
    let uu____6334 = cur_goal ()  in
    bind uu____6334
      (fun goal  ->
         let uu____6340 =
           let uu____6347 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6347  in
         match uu____6340 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6363 =
                 let uu____6366 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6366  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6363
                in
             let uu____6381 = new_uvar "revert" env' typ'  in
             bind uu____6381
               (fun uu____6396  ->
                  match uu____6396 with
                  | (r,u_r) ->
                      let uu____6405 =
                        let uu____6408 =
                          let uu____6409 =
                            let uu____6410 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6410.FStar_Syntax_Syntax.pos  in
                          let uu____6413 =
                            let uu____6418 =
                              let uu____6419 =
                                let uu____6428 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6428  in
                              [uu____6419]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6418  in
                          uu____6413 FStar_Pervasives_Native.None uu____6409
                           in
                        set_solution goal uu____6408  in
                      bind uu____6405
                        (fun uu____6449  ->
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
      let uu____6461 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6461
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6476 = cur_goal ()  in
    bind uu____6476
      (fun goal  ->
         mlog
           (fun uu____6484  ->
              let uu____6485 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6486 =
                let uu____6487 =
                  let uu____6488 =
                    let uu____6497 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6497  in
                  FStar_All.pipe_right uu____6488 FStar_List.length  in
                FStar_All.pipe_right uu____6487 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6485 uu____6486)
           (fun uu____6514  ->
              let uu____6515 =
                let uu____6524 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6524  in
              match uu____6515 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6563 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6563
                        then
                          let uu____6566 =
                            let uu____6567 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6567
                             in
                          fail uu____6566
                        else check1 bvs2
                     in
                  let uu____6569 =
                    let uu____6570 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6570  in
                  if uu____6569
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6574 = check1 bvs  in
                     bind uu____6574
                       (fun uu____6580  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6582 =
                            let uu____6589 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6589  in
                          bind uu____6582
                            (fun uu____6598  ->
                               match uu____6598 with
                               | (ut,uvar_ut) ->
                                   let uu____6607 = set_solution goal ut  in
                                   bind uu____6607
                                     (fun uu____6612  ->
                                        let uu____6613 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6613))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6620  ->
    let uu____6623 = cur_goal ()  in
    bind uu____6623
      (fun goal  ->
         let uu____6629 =
           let uu____6636 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6636  in
         match uu____6629 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6644) ->
             let uu____6649 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6649)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6659 = cur_goal ()  in
    bind uu____6659
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6669 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6669  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6672  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6682 = cur_goal ()  in
    bind uu____6682
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6692 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6692  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6695  -> add_goals [g']))
  
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
            let uu____6735 = FStar_Syntax_Subst.compress t  in
            uu____6735.FStar_Syntax_Syntax.n  in
          let uu____6738 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___403_6744 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___403_6744.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___403_6744.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6738
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6760 =
                   let uu____6761 = FStar_Syntax_Subst.compress t1  in
                   uu____6761.FStar_Syntax_Syntax.n  in
                 match uu____6760 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6792 = ff hd1  in
                     bind uu____6792
                       (fun hd2  ->
                          let fa uu____6818 =
                            match uu____6818 with
                            | (a,q) ->
                                let uu____6839 = ff a  in
                                bind uu____6839 (fun a1  -> ret (a1, q))
                             in
                          let uu____6858 = mapM fa args  in
                          bind uu____6858
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6940 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6940 with
                      | (bs1,t') ->
                          let uu____6949 =
                            let uu____6952 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6952 t'  in
                          bind uu____6949
                            (fun t''  ->
                               let uu____6956 =
                                 let uu____6957 =
                                   let uu____6976 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6985 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6976, uu____6985, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6957  in
                               ret uu____6956))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7060 = ff hd1  in
                     bind uu____7060
                       (fun hd2  ->
                          let ffb br =
                            let uu____7075 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7075 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7107 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7107  in
                                let uu____7108 = ff1 e  in
                                bind uu____7108
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7123 = mapM ffb brs  in
                          bind uu____7123
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7167;
                          FStar_Syntax_Syntax.lbtyp = uu____7168;
                          FStar_Syntax_Syntax.lbeff = uu____7169;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7171;
                          FStar_Syntax_Syntax.lbpos = uu____7172;_}::[]),e)
                     ->
                     let lb =
                       let uu____7197 =
                         let uu____7198 = FStar_Syntax_Subst.compress t1  in
                         uu____7198.FStar_Syntax_Syntax.n  in
                       match uu____7197 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7202) -> lb
                       | uu____7215 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7224 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7224
                         (fun def1  ->
                            ret
                              (let uu___400_7230 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___400_7230.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___400_7230.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___400_7230.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___400_7230.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___400_7230.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___400_7230.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7231 = fflb lb  in
                     bind uu____7231
                       (fun lb1  ->
                          let uu____7241 =
                            let uu____7246 =
                              let uu____7247 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7247]  in
                            FStar_Syntax_Subst.open_term uu____7246 e  in
                          match uu____7241 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7277 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7277  in
                              let uu____7278 = ff1 e1  in
                              bind uu____7278
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7319 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7319
                         (fun def  ->
                            ret
                              (let uu___401_7325 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___401_7325.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___401_7325.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___401_7325.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___401_7325.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___401_7325.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___401_7325.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7326 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7326 with
                      | (lbs1,e1) ->
                          let uu____7341 = mapM fflb lbs1  in
                          bind uu____7341
                            (fun lbs2  ->
                               let uu____7353 = ff e1  in
                               bind uu____7353
                                 (fun e2  ->
                                    let uu____7361 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7361 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7429 = ff t2  in
                     bind uu____7429
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7460 = ff t2  in
                     bind uu____7460
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7467 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___402_7474 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___402_7474.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___402_7474.FStar_Syntax_Syntax.vars)
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
            let uu____7511 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___404_7520 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___404_7520.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___404_7520.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___404_7520.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___404_7520.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___404_7520.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___404_7520.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___404_7520.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___404_7520.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___404_7520.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___404_7520.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___404_7520.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___404_7520.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___404_7520.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___404_7520.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___404_7520.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___404_7520.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___404_7520.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___404_7520.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___404_7520.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___404_7520.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___404_7520.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___404_7520.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___404_7520.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___404_7520.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___404_7520.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___404_7520.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___404_7520.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___404_7520.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___404_7520.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___404_7520.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___404_7520.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___404_7520.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___404_7520.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___404_7520.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___404_7520.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___404_7520.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___404_7520.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___404_7520.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___404_7520.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___404_7520.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___404_7520.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7511 with
            | (t1,lcomp,g) ->
                let uu____7526 =
                  (let uu____7529 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7529) ||
                    (let uu____7531 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7531)
                   in
                if uu____7526
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7539 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7539
                       (fun uu____7555  ->
                          match uu____7555 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7568  ->
                                    let uu____7569 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7570 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7569 uu____7570);
                               (let uu____7571 =
                                  let uu____7574 =
                                    let uu____7575 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7575 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7574
                                    opts
                                   in
                                bind uu____7571
                                  (fun uu____7578  ->
                                     let uu____7579 =
                                       bind tau
                                         (fun uu____7585  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7591  ->
                                                 let uu____7592 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7593 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7592 uu____7593);
                                            ret ut1)
                                        in
                                     focus uu____7579))))
                      in
                   let uu____7594 = trytac' rewrite_eq  in
                   bind uu____7594
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
          let uu____7792 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7792
            (fun t1  ->
               let uu____7800 =
                 f env
                   (let uu___407_7809 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___407_7809.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___407_7809.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7800
                 (fun uu____7825  ->
                    match uu____7825 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7848 =
                               let uu____7849 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7849.FStar_Syntax_Syntax.n  in
                             match uu____7848 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7886 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7886
                                   (fun uu____7911  ->
                                      match uu____7911 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7927 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7927
                                            (fun uu____7954  ->
                                               match uu____7954 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___405_7984 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___405_7984.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___405_7984.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8026 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8026 with
                                  | (bs1,t') ->
                                      let uu____8041 =
                                        let uu____8048 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8048 ctrl1 t'
                                         in
                                      bind uu____8041
                                        (fun uu____8066  ->
                                           match uu____8066 with
                                           | (t'',ctrl2) ->
                                               let uu____8081 =
                                                 let uu____8088 =
                                                   let uu___406_8091 = t4  in
                                                   let uu____8094 =
                                                     let uu____8095 =
                                                       let uu____8114 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8123 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8114,
                                                         uu____8123, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8095
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8094;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___406_8091.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___406_8091.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8088, ctrl2)  in
                                               ret uu____8081))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8176 -> ret (t3, ctrl1))))

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
              let uu____8223 = ctrl_tac_fold f env ctrl t  in
              bind uu____8223
                (fun uu____8247  ->
                   match uu____8247 with
                   | (t1,ctrl1) ->
                       let uu____8262 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8262
                         (fun uu____8289  ->
                            match uu____8289 with
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
              let uu____8373 =
                let uu____8380 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8380
                  (fun uu____8389  ->
                     let uu____8390 = ctrl t1  in
                     bind uu____8390
                       (fun res  ->
                          let uu____8413 = trivial ()  in
                          bind uu____8413 (fun uu____8421  -> ret res)))
                 in
              bind uu____8373
                (fun uu____8437  ->
                   match uu____8437 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8461 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___408_8470 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___408_8470.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___408_8470.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___408_8470.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___408_8470.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___408_8470.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___408_8470.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___408_8470.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___408_8470.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___408_8470.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___408_8470.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___408_8470.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___408_8470.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___408_8470.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___408_8470.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___408_8470.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___408_8470.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___408_8470.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___408_8470.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___408_8470.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___408_8470.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___408_8470.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___408_8470.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___408_8470.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___408_8470.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___408_8470.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___408_8470.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___408_8470.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___408_8470.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___408_8470.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___408_8470.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___408_8470.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___408_8470.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___408_8470.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___408_8470.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___408_8470.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___408_8470.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___408_8470.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___408_8470.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___408_8470.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___408_8470.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___408_8470.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8461 with
                          | (t2,lcomp,g) ->
                              let uu____8480 =
                                (let uu____8483 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8483) ||
                                  (let uu____8485 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8485)
                                 in
                              if uu____8480
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8498 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8498
                                   (fun uu____8518  ->
                                      match uu____8518 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8535  ->
                                                let uu____8536 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8537 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8536 uu____8537);
                                           (let uu____8538 =
                                              let uu____8541 =
                                                let uu____8542 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8542 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8541 opts
                                               in
                                            bind uu____8538
                                              (fun uu____8549  ->
                                                 let uu____8550 =
                                                   bind rewriter
                                                     (fun uu____8564  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8570  ->
                                                             let uu____8571 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8572 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8571
                                                               uu____8572);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8550)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8613 =
        bind get
          (fun ps  ->
             let uu____8623 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8623 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8660  ->
                       let uu____8661 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8661);
                  bind dismiss_all
                    (fun uu____8664  ->
                       let uu____8665 =
                         let uu____8672 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8672
                           keepGoing gt1
                          in
                       bind uu____8665
                         (fun uu____8684  ->
                            match uu____8684 with
                            | (gt',uu____8692) ->
                                (log ps
                                   (fun uu____8696  ->
                                      let uu____8697 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8697);
                                 (let uu____8698 = push_goals gs  in
                                  bind uu____8698
                                    (fun uu____8703  ->
                                       let uu____8704 =
                                         let uu____8707 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8707]  in
                                       add_goals uu____8704)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8613
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8730 =
        bind get
          (fun ps  ->
             let uu____8740 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8740 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8777  ->
                       let uu____8778 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8778);
                  bind dismiss_all
                    (fun uu____8781  ->
                       let uu____8782 =
                         let uu____8785 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8785 gt1
                          in
                       bind uu____8782
                         (fun gt'  ->
                            log ps
                              (fun uu____8793  ->
                                 let uu____8794 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8794);
                            (let uu____8795 = push_goals gs  in
                             bind uu____8795
                               (fun uu____8800  ->
                                  let uu____8801 =
                                    let uu____8804 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8804]  in
                                  add_goals uu____8801))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8730
  
let (trefl : unit -> unit tac) =
  fun uu____8815  ->
    let uu____8818 =
      let uu____8821 = cur_goal ()  in
      bind uu____8821
        (fun g  ->
           let uu____8839 =
             let uu____8844 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8844  in
           match uu____8839 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8852 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8852 with
                | (hd1,args) ->
                    let uu____8891 =
                      let uu____8904 =
                        let uu____8905 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8905.FStar_Syntax_Syntax.n  in
                      (uu____8904, args)  in
                    (match uu____8891 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8919::(l,uu____8921)::(r,uu____8923)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8970 =
                           let uu____8973 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8973 l r  in
                         bind uu____8970
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8980 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8980 l
                                    in
                                 let r1 =
                                   let uu____8982 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8982 r
                                    in
                                 let uu____8983 =
                                   let uu____8986 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8986 l1 r1  in
                                 bind uu____8983
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8992 =
                                           let uu____8993 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8993 l1  in
                                         let uu____8994 =
                                           let uu____8995 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8995 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8992 uu____8994))))
                     | (hd2,uu____8997) ->
                         let uu____9014 =
                           let uu____9015 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9015 t  in
                         fail1 "trefl: not an equality (%s)" uu____9014))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8818
  
let (dup : unit -> unit tac) =
  fun uu____9028  ->
    let uu____9031 = cur_goal ()  in
    bind uu____9031
      (fun g  ->
         let uu____9037 =
           let uu____9044 = FStar_Tactics_Types.goal_env g  in
           let uu____9045 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9044 uu____9045  in
         bind uu____9037
           (fun uu____9054  ->
              match uu____9054 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___409_9064 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___409_9064.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___409_9064.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___409_9064.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9067  ->
                       let uu____9068 =
                         let uu____9071 = FStar_Tactics_Types.goal_env g  in
                         let uu____9072 =
                           let uu____9073 =
                             let uu____9074 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9075 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9074
                               uu____9075
                              in
                           let uu____9076 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9077 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9073 uu____9076 u
                             uu____9077
                            in
                         add_irrelevant_goal "dup equation" uu____9071
                           uu____9072 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9068
                         (fun uu____9080  ->
                            let uu____9081 = add_goals [g']  in
                            bind uu____9081 (fun uu____9085  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9092  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___410_9109 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___410_9109.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___410_9109.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___410_9109.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___410_9109.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___410_9109.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___410_9109.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___410_9109.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___410_9109.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___410_9109.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___410_9109.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___410_9109.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9110 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9119  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___411_9132 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___411_9132.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___411_9132.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___411_9132.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___411_9132.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___411_9132.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___411_9132.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___411_9132.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___411_9132.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___411_9132.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___411_9132.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___411_9132.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9139  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9146 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9166 =
      let uu____9173 = cur_goal ()  in
      bind uu____9173
        (fun g  ->
           let uu____9183 =
             let uu____9192 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9192 t  in
           bind uu____9183
             (fun uu____9220  ->
                match uu____9220 with
                | (t1,typ,guard) ->
                    let uu____9236 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9236 with
                     | (hd1,args) ->
                         let uu____9285 =
                           let uu____9300 =
                             let uu____9301 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9301.FStar_Syntax_Syntax.n  in
                           (uu____9300, args)  in
                         (match uu____9285 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9322)::(q,uu____9324)::[]) when
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
                                let uu____9378 =
                                  let uu____9379 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9379
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9378
                                 in
                              let g2 =
                                let uu____9381 =
                                  let uu____9382 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9382
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9381
                                 in
                              bind __dismiss
                                (fun uu____9389  ->
                                   let uu____9390 = add_goals [g1; g2]  in
                                   bind uu____9390
                                     (fun uu____9399  ->
                                        let uu____9400 =
                                          let uu____9405 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9406 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9405, uu____9406)  in
                                        ret uu____9400))
                          | uu____9411 ->
                              let uu____9426 =
                                let uu____9427 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9427 typ  in
                              fail1 "Not a disjunction: %s" uu____9426))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9166
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9457 =
      let uu____9460 = cur_goal ()  in
      bind uu____9460
        (fun g  ->
           FStar_Options.push ();
           (let uu____9473 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9473);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___412_9480 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___412_9480.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___412_9480.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___412_9480.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9457
  
let (top_env : unit -> env tac) =
  fun uu____9492  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9505  ->
    let uu____9508 = cur_goal ()  in
    bind uu____9508
      (fun g  ->
         let uu____9514 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9514)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9523  ->
    let uu____9526 = cur_goal ()  in
    bind uu____9526
      (fun g  ->
         let uu____9532 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9532)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9541  ->
    let uu____9544 = cur_goal ()  in
    bind uu____9544
      (fun g  ->
         let uu____9550 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9550)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9559  ->
    let uu____9562 = cur_env ()  in
    bind uu____9562
      (fun e  ->
         let uu____9568 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____9568)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9583 =
        mlog
          (fun uu____9588  ->
             let uu____9589 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9589)
          (fun uu____9592  ->
             let uu____9593 = cur_goal ()  in
             bind uu____9593
               (fun goal  ->
                  let env =
                    let uu____9601 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9601 ty  in
                  let uu____9602 = __tc env tm  in
                  bind uu____9602
                    (fun uu____9621  ->
                       match uu____9621 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9635  ->
                                let uu____9636 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9636)
                             (fun uu____9638  ->
                                mlog
                                  (fun uu____9641  ->
                                     let uu____9642 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9642)
                                  (fun uu____9645  ->
                                     let uu____9646 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9646
                                       (fun uu____9650  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9583
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9673 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9679 =
              let uu____9686 =
                let uu____9687 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9687
                 in
              new_uvar "uvar_env.2" env uu____9686  in
            bind uu____9679
              (fun uu____9703  ->
                 match uu____9703 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9673
        (fun typ  ->
           let uu____9715 = new_uvar "uvar_env" env typ  in
           bind uu____9715
             (fun uu____9729  -> match uu____9729 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9747 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9766 -> g.FStar_Tactics_Types.opts
             | uu____9769 -> FStar_Options.peek ()  in
           let uu____9772 = FStar_Syntax_Util.head_and_args t  in
           match uu____9772 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9792);
                FStar_Syntax_Syntax.pos = uu____9793;
                FStar_Syntax_Syntax.vars = uu____9794;_},uu____9795)
               ->
               let env1 =
                 let uu___413_9837 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___413_9837.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___413_9837.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___413_9837.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___413_9837.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___413_9837.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___413_9837.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___413_9837.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___413_9837.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___413_9837.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___413_9837.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___413_9837.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___413_9837.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___413_9837.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___413_9837.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___413_9837.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___413_9837.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___413_9837.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___413_9837.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___413_9837.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___413_9837.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___413_9837.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___413_9837.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___413_9837.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___413_9837.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___413_9837.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___413_9837.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___413_9837.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___413_9837.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___413_9837.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___413_9837.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___413_9837.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___413_9837.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___413_9837.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___413_9837.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___413_9837.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___413_9837.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___413_9837.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___413_9837.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___413_9837.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___413_9837.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___413_9837.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9839 =
                 let uu____9842 = bnorm_goal g  in [uu____9842]  in
               add_goals uu____9839
           | uu____9843 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9747
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9892 = if b then t2 else ret false  in
             bind uu____9892 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9903 = trytac comp  in
      bind uu____9903
        (fun uu___350_9911  ->
           match uu___350_9911 with
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
        let uu____9937 =
          bind get
            (fun ps  ->
               let uu____9943 = __tc e t1  in
               bind uu____9943
                 (fun uu____9963  ->
                    match uu____9963 with
                    | (t11,ty1,g1) ->
                        let uu____9975 = __tc e t2  in
                        bind uu____9975
                          (fun uu____9995  ->
                             match uu____9995 with
                             | (t21,ty2,g2) ->
                                 let uu____10007 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10007
                                   (fun uu____10012  ->
                                      let uu____10013 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10013
                                        (fun uu____10019  ->
                                           let uu____10020 =
                                             do_unify e ty1 ty2  in
                                           let uu____10023 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10020 uu____10023)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9937
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10056  ->
             let uu____10057 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10057
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
        (fun uu____10078  ->
           let uu____10079 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10079)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10089 =
      mlog
        (fun uu____10094  ->
           let uu____10095 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10095)
        (fun uu____10098  ->
           let uu____10099 = cur_goal ()  in
           bind uu____10099
             (fun g  ->
                let uu____10105 =
                  let uu____10114 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10114 ty  in
                bind uu____10105
                  (fun uu____10126  ->
                     match uu____10126 with
                     | (ty1,uu____10136,guard) ->
                         let uu____10138 =
                           let uu____10141 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10141 guard  in
                         bind uu____10138
                           (fun uu____10144  ->
                              let uu____10145 =
                                let uu____10148 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10149 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10148 uu____10149 ty1  in
                              bind uu____10145
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10155 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10155
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.Reify;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify;
                                        FStar_TypeChecker_Env.UnfoldTac;
                                        FStar_TypeChecker_Env.Unmeta]  in
                                      let ng =
                                        let uu____10161 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10162 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10161
                                          uu____10162
                                         in
                                      let nty =
                                        let uu____10164 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10164 ty1  in
                                      let uu____10165 =
                                        let uu____10168 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10168 ng nty  in
                                      bind uu____10165
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10174 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10174
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10089
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10237 =
      let uu____10246 = cur_goal ()  in
      bind uu____10246
        (fun g  ->
           let uu____10258 =
             let uu____10267 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10267 s_tm  in
           bind uu____10258
             (fun uu____10285  ->
                match uu____10285 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10303 =
                      let uu____10306 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10306 guard  in
                    bind uu____10303
                      (fun uu____10318  ->
                         let uu____10319 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10319 with
                         | (h,args) ->
                             let uu____10364 =
                               let uu____10371 =
                                 let uu____10372 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10372.FStar_Syntax_Syntax.n  in
                               match uu____10371 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10387;
                                      FStar_Syntax_Syntax.vars = uu____10388;_},us)
                                   -> ret (fv, us)
                               | uu____10398 -> fail "type is not an fv"  in
                             bind uu____10364
                               (fun uu____10418  ->
                                  match uu____10418 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10434 =
                                        let uu____10437 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10437 t_lid
                                         in
                                      (match uu____10434 with
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
                                                  (fun uu____10486  ->
                                                     let uu____10487 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10487 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10502 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10530
                                                                  =
                                                                  let uu____10533
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10533
                                                                    c_lid
                                                                   in
                                                                match uu____10530
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
                                                                    uu____10603
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
                                                                    let uu____10608
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10608
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10631
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10631
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10674
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10674
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____10747
                                                                    =
                                                                    let uu____10748
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____10748
                                                                     in
                                                                    failwhen
                                                                    uu____10747
                                                                    "not total?"
                                                                    (fun
                                                                    uu____10765
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
                                                                    uu___351_10781
                                                                    =
                                                                    match uu___351_10781
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____10784)
                                                                    -> true
                                                                    | 
                                                                    uu____10785
                                                                    -> false
                                                                     in
                                                                    let uu____10788
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____10788
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
                                                                    uu____10921
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
                                                                    uu____10983
                                                                     ->
                                                                    match uu____10983
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11003),
                                                                    (t,uu____11005))
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
                                                                    uu____11073
                                                                     ->
                                                                    match uu____11073
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11099),
                                                                    (t,uu____11101))
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
                                                                    uu____11156
                                                                     ->
                                                                    match uu____11156
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
                                                                    let uu____11206
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___414_11223
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___414_11223.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11206
                                                                    with
                                                                    | 
                                                                    (uu____11236,uu____11237,uu____11238,pat_t,uu____11240,uu____11241)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11247
                                                                    =
                                                                    let uu____11248
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11248
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11247
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11252
                                                                    =
                                                                    let uu____11261
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11261]
                                                                     in
                                                                    let uu____11280
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11252
                                                                    uu____11280
                                                                     in
                                                                    let nty =
                                                                    let uu____11286
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11286
                                                                     in
                                                                    let uu____11289
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11289
                                                                    (fun
                                                                    uu____11318
                                                                     ->
                                                                    match uu____11318
                                                                    with
                                                                    | 
                                                                    (uvt,uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false  in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs2
                                                                     in
                                                                    let brt1
                                                                    =
                                                                    let uu____11344
                                                                    =
                                                                    let uu____11355
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11355]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11344
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11391
                                                                    =
                                                                    let uu____11402
                                                                    =
                                                                    let uu____11407
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11407)
                                                                     in
                                                                    (g', br,
                                                                    uu____11402)
                                                                     in
                                                                    ret
                                                                    uu____11391))))))
                                                                    | 
                                                                    uu____11428
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10502
                                                           (fun goal_brs  ->
                                                              let uu____11477
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11477
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
                                                                  let uu____11550
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11550
                                                                    (
                                                                    fun
                                                                    uu____11561
                                                                     ->
                                                                    let uu____11562
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11562
                                                                    (fun
                                                                    uu____11572
                                                                     ->
                                                                    ret infos))))
                                            | uu____11579 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10237
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11624::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11652 = init xs  in x :: uu____11652
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11664 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____11673) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____11738 = last args  in
          (match uu____11738 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____11768 =
                 let uu____11769 =
                   let uu____11774 =
                     let uu____11775 =
                       let uu____11780 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____11780  in
                     uu____11775 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____11774, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____11769  in
               FStar_All.pipe_left ret uu____11768)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____11793,uu____11794) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____11846 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____11846 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____11887 =
                      let uu____11888 =
                        let uu____11893 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____11893)  in
                      FStar_Reflection_Data.Tv_Abs uu____11888  in
                    FStar_All.pipe_left ret uu____11887))
      | FStar_Syntax_Syntax.Tm_type uu____11896 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____11920 ->
          let uu____11935 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____11935 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____11965 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____11965 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12018 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12030 =
            let uu____12031 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12031  in
          FStar_All.pipe_left ret uu____12030
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12052 =
            let uu____12053 =
              let uu____12058 =
                let uu____12059 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12059  in
              (uu____12058, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12053  in
          FStar_All.pipe_left ret uu____12052
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12093 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12098 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12098 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12151 ->
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
             | FStar_Util.Inr uu____12185 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12189 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12189 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12209 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12213 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12267 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12267
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12286 =
                  let uu____12293 =
                    FStar_List.map
                      (fun uu____12305  ->
                         match uu____12305 with
                         | (p1,uu____12313) -> inspect_pat p1) ps
                     in
                  (fv, uu____12293)  in
                FStar_Reflection_Data.Pat_Cons uu____12286
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
              (fun uu___352_12407  ->
                 match uu___352_12407 with
                 | (pat,uu____12429,t5) ->
                     let uu____12447 = inspect_pat pat  in (uu____12447, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12456 ->
          ((let uu____12458 =
              let uu____12463 =
                let uu____12464 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12465 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12464 uu____12465
                 in
              (FStar_Errors.Warning_CantInspect, uu____12463)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12458);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11664
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12478 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12478
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12482 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12482
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12486 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12486
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12493 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12493
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12518 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12518
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12535 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12535
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12554 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12554
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12558 =
          let uu____12559 =
            let uu____12566 =
              let uu____12567 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12567  in
            FStar_Syntax_Syntax.mk uu____12566  in
          uu____12559 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12558
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12575 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12575
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12584 =
          let uu____12585 =
            let uu____12592 =
              let uu____12593 =
                let uu____12606 =
                  let uu____12609 =
                    let uu____12610 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12610]  in
                  FStar_Syntax_Subst.close uu____12609 t2  in
                ((false, [lb]), uu____12606)  in
              FStar_Syntax_Syntax.Tm_let uu____12593  in
            FStar_Syntax_Syntax.mk uu____12592  in
          uu____12585 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12584
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12650 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12650 with
         | (lbs,body) ->
             let uu____12665 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12665)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12699 =
                let uu____12700 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12700  in
              FStar_All.pipe_left wrap uu____12699
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12707 =
                let uu____12708 =
                  let uu____12721 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____12737 = pack_pat p1  in
                         (uu____12737, false)) ps
                     in
                  (fv, uu____12721)  in
                FStar_Syntax_Syntax.Pat_cons uu____12708  in
              FStar_All.pipe_left wrap uu____12707
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
            (fun uu___353_12783  ->
               match uu___353_12783 with
               | (pat,t1) ->
                   let uu____12800 = pack_pat pat  in
                   (uu____12800, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____12848 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12848
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____12876 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12876
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12922 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12922
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____12961 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12961
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____12982 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____12982 with
      | (u,ctx_uvars,g_u) ->
          let uu____13014 = FStar_List.hd ctx_uvars  in
          (match uu____13014 with
           | (ctx_uvar,uu____13028) ->
               let g =
                 let uu____13030 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13030 false
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
        let uu____13050 = goal_of_goal_ty env typ  in
        match uu____13050 with
        | (g,g_u) ->
            let ps =
              let uu____13062 =
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
                FStar_Tactics_Types.psc = FStar_TypeChecker_Cfg.null_psc;
                FStar_Tactics_Types.entry_range = rng;
                FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
                FStar_Tactics_Types.freshness = (Prims.parse_int "0");
                FStar_Tactics_Types.tac_verb_dbg = uu____13062
              }  in
            let uu____13067 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13067)
  