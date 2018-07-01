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
             (fun uu____2392  ->
                match uu____2392 with
                | (t1,typ,guard) ->
                    let uu____2404 =
                      let uu____2407 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2407 guard  in
                    bind uu____2404 (fun uu____2409  -> ret typ)))
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
          let uu____2438 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2438 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2449  ->
    let uu____2452 = cur_goal ()  in
    bind uu____2452
      (fun goal  ->
         let uu____2458 =
           let uu____2459 = FStar_Tactics_Types.goal_env goal  in
           let uu____2460 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2459 uu____2460  in
         if uu____2458
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2464 =
              let uu____2465 = FStar_Tactics_Types.goal_env goal  in
              let uu____2466 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2465 uu____2466  in
            fail1 "Not a trivial goal: %s" uu____2464))
  
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
          let uu____2495 =
            let uu____2496 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2496.FStar_TypeChecker_Env.guard_f  in
          match uu____2495 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2504 = istrivial e f  in
              if uu____2504
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2512 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2512
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___380_2522 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___380_2522.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___380_2522.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___380_2522.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2529  ->
    let uu____2532 = cur_goal ()  in
    bind uu____2532
      (fun g  ->
         let uu____2538 = is_irrelevant g  in
         if uu____2538
         then bind __dismiss (fun uu____2542  -> add_smt_goals [g])
         else
           (let uu____2544 =
              let uu____2545 = FStar_Tactics_Types.goal_env g  in
              let uu____2546 = FStar_Tactics_Types.goal_type g  in
              tts uu____2545 uu____2546  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2544))
  
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
             let uu____2595 =
               try
                 let uu____2629 =
                   let uu____2638 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2638 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2629
               with | uu____2660 -> fail "divide: not enough goals"  in
             bind uu____2595
               (fun uu____2686  ->
                  match uu____2686 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___381_2712 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___381_2712.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___381_2712.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___381_2712.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___381_2712.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___381_2712.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___381_2712.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___381_2712.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___381_2712.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___381_2712.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___381_2712.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2713 = set lp  in
                      bind uu____2713
                        (fun uu____2721  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___382_2737 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___382_2737.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___382_2737.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___382_2737.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___382_2737.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___382_2737.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___382_2737.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___382_2737.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___382_2737.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___382_2737.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___382_2737.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2738 = set rp  in
                                     bind uu____2738
                                       (fun uu____2746  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___383_2762 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___383_2762.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___383_2762.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2763 = set p'
                                                       in
                                                    bind uu____2763
                                                      (fun uu____2771  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2777 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2798 = divide FStar_BigInt.one f idtac  in
    bind uu____2798
      (fun uu____2811  -> match uu____2811 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2848::uu____2849 ->
             let uu____2852 =
               let uu____2861 = map tau  in
               divide FStar_BigInt.one tau uu____2861  in
             bind uu____2852
               (fun uu____2879  ->
                  match uu____2879 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2920 =
        bind t1
          (fun uu____2925  ->
             let uu____2926 = map t2  in
             bind uu____2926 (fun uu____2934  -> ret ()))
         in
      focus uu____2920
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2943  ->
    let uu____2946 =
      let uu____2949 = cur_goal ()  in
      bind uu____2949
        (fun goal  ->
           let uu____2958 =
             let uu____2965 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2965  in
           match uu____2958 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2974 =
                 let uu____2975 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2975  in
               if uu____2974
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2980 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2980 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2994 = new_uvar "intro" env' typ'  in
                  bind uu____2994
                    (fun uu____3010  ->
                       match uu____3010 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3034 = set_solution goal sol  in
                           bind uu____3034
                             (fun uu____3040  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3042 =
                                  let uu____3045 = bnorm_goal g  in
                                  replace_cur uu____3045  in
                                bind uu____3042 (fun uu____3047  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3052 =
                 let uu____3053 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3054 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3053 uu____3054  in
               fail1 "goal is not an arrow (%s)" uu____3052)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2946
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3069  ->
    let uu____3076 = cur_goal ()  in
    bind uu____3076
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3093 =
            let uu____3100 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3100  in
          match uu____3093 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3113 =
                let uu____3114 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3114  in
              if uu____3113
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3127 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3127
                    in
                 let bs =
                   let uu____3137 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3137; b]  in
                 let env' =
                   let uu____3163 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3163 bs  in
                 let uu____3164 =
                   let uu____3171 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3171  in
                 bind uu____3164
                   (fun uu____3190  ->
                      match uu____3190 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3204 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3207 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3204
                              FStar_Parser_Const.effect_Tot_lid uu____3207 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3225 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3225 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3247 =
                                   let uu____3248 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3248.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3247
                                  in
                               let uu____3261 = set_solution goal tm  in
                               bind uu____3261
                                 (fun uu____3270  ->
                                    let uu____3271 =
                                      let uu____3274 =
                                        bnorm_goal
                                          (let uu___386_3277 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___386_3277.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___386_3277.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___386_3277.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3274  in
                                    bind uu____3271
                                      (fun uu____3284  ->
                                         let uu____3285 =
                                           let uu____3290 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3290, b)  in
                                         ret uu____3285)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3299 =
                let uu____3300 = FStar_Tactics_Types.goal_env goal  in
                let uu____3301 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3300 uu____3301  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3299))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3319 = cur_goal ()  in
    bind uu____3319
      (fun goal  ->
         mlog
           (fun uu____3326  ->
              let uu____3327 =
                let uu____3328 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3328  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3327)
           (fun uu____3333  ->
              let steps =
                let uu____3337 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3337
                 in
              let t =
                let uu____3341 = FStar_Tactics_Types.goal_env goal  in
                let uu____3342 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3341 uu____3342  in
              let uu____3343 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3343))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3367 =
          mlog
            (fun uu____3372  ->
               let uu____3373 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3373)
            (fun uu____3375  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3381 -> g.FStar_Tactics_Types.opts
                      | uu____3384 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3389  ->
                         let uu____3390 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3390)
                      (fun uu____3393  ->
                         let uu____3394 = __tc e t  in
                         bind uu____3394
                           (fun uu____3415  ->
                              match uu____3415 with
                              | (t1,uu____3425,uu____3426) ->
                                  let steps =
                                    let uu____3430 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3430
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3367
  
let (refine_intro : unit -> unit tac) =
  fun uu____3444  ->
    let uu____3447 =
      let uu____3450 = cur_goal ()  in
      bind uu____3450
        (fun g  ->
           let uu____3457 =
             let uu____3468 = FStar_Tactics_Types.goal_env g  in
             let uu____3469 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3468 uu____3469
              in
           match uu____3457 with
           | (uu____3472,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3497 =
                 let uu____3502 =
                   let uu____3507 =
                     let uu____3508 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3508]  in
                   FStar_Syntax_Subst.open_term uu____3507 phi  in
                 match uu____3502 with
                 | (bvs,phi1) ->
                     let uu____3533 =
                       let uu____3534 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3534  in
                     (uu____3533, phi1)
                  in
               (match uu____3497 with
                | (bv1,phi1) ->
                    let uu____3553 =
                      let uu____3556 = FStar_Tactics_Types.goal_env g  in
                      let uu____3557 =
                        let uu____3558 =
                          let uu____3561 =
                            let uu____3562 =
                              let uu____3569 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3569)  in
                            FStar_Syntax_Syntax.NT uu____3562  in
                          [uu____3561]  in
                        FStar_Syntax_Subst.subst uu____3558 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3556
                        uu____3557 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3553
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3577  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3447
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3596 = cur_goal ()  in
      bind uu____3596
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3604 = FStar_Tactics_Types.goal_env goal  in
               let uu____3605 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3604 uu____3605
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3607 = __tc env t  in
           bind uu____3607
             (fun uu____3626  ->
                match uu____3626 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3641  ->
                         let uu____3642 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3643 =
                           let uu____3644 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3644
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3642 uu____3643)
                      (fun uu____3647  ->
                         let uu____3648 =
                           let uu____3651 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3651 guard  in
                         bind uu____3648
                           (fun uu____3653  ->
                              mlog
                                (fun uu____3657  ->
                                   let uu____3658 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3659 =
                                     let uu____3660 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3660
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3658 uu____3659)
                                (fun uu____3663  ->
                                   let uu____3664 =
                                     let uu____3667 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3668 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3667 typ uu____3668  in
                                   bind uu____3664
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3674 =
                                             let uu____3675 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3675 t1  in
                                           let uu____3676 =
                                             let uu____3677 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3677 typ  in
                                           let uu____3678 =
                                             let uu____3679 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3680 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3679 uu____3680  in
                                           let uu____3681 =
                                             let uu____3682 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3683 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3682 uu____3683  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3674 uu____3676 uu____3678
                                             uu____3681)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3698 =
        mlog
          (fun uu____3703  ->
             let uu____3704 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3704)
          (fun uu____3707  ->
             let uu____3708 =
               let uu____3715 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3715  in
             bind uu____3708
               (fun uu___348_3724  ->
                  match uu___348_3724 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3734  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3737  ->
                           let uu____3738 =
                             let uu____3745 =
                               let uu____3748 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3748
                                 (fun uu____3753  ->
                                    let uu____3754 = refine_intro ()  in
                                    bind uu____3754
                                      (fun uu____3758  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3745  in
                           bind uu____3738
                             (fun uu___347_3765  ->
                                match uu___347_3765 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3773 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3698
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3823 = f x  in
          bind uu____3823
            (fun y  ->
               let uu____3831 = mapM f xs  in
               bind uu____3831 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3902 = do_unify e ty1 ty2  in
          bind uu____3902
            (fun uu___349_3914  ->
               if uu___349_3914
               then ret acc
               else
                 (let uu____3933 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3933 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3954 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3955 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3954
                        uu____3955
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3970 =
                        let uu____3971 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3971  in
                      if uu____3970
                      then fail "Codomain is effectful"
                      else
                        (let uu____3991 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3991
                           (fun uu____4017  ->
                              match uu____4017 with
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
      let uu____4103 =
        mlog
          (fun uu____4108  ->
             let uu____4109 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4109)
          (fun uu____4112  ->
             let uu____4113 = cur_goal ()  in
             bind uu____4113
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4121 = __tc e tm  in
                  bind uu____4121
                    (fun uu____4142  ->
                       match uu____4142 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4155 =
                             let uu____4166 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4166  in
                           bind uu____4155
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4209  ->
                                       fun w  ->
                                         match uu____4209 with
                                         | (uvt,q,uu____4227) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4259 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4276  ->
                                       fun s  ->
                                         match uu____4276 with
                                         | (uu____4288,uu____4289,uv) ->
                                             let uu____4291 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4291) uvs uu____4259
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4300 = solve' goal w  in
                                bind uu____4300
                                  (fun uu____4305  ->
                                     let uu____4306 =
                                       mapM
                                         (fun uu____4323  ->
                                            match uu____4323 with
                                            | (uvt,q,uv) ->
                                                let uu____4335 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4335 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4340 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4341 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4341
                                                     then ret ()
                                                     else
                                                       (let uu____4345 =
                                                          let uu____4348 =
                                                            bnorm_goal
                                                              (let uu___387_4351
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___387_4351.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___387_4351.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4348]  in
                                                        add_goals uu____4345)))
                                         uvs
                                        in
                                     bind uu____4306
                                       (fun uu____4355  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4103
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4380 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4380
    then
      let uu____4387 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4402 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4455 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4387 with
      | (pre,post) ->
          let post1 =
            let uu____4487 =
              let uu____4498 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4498]  in
            FStar_Syntax_Util.mk_app post uu____4487  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4528 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4528
       then
         let uu____4535 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4535
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4568 =
      let uu____4571 =
        mlog
          (fun uu____4576  ->
             let uu____4577 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4577)
          (fun uu____4581  ->
             let is_unit_t t =
               let uu____4588 =
                 let uu____4589 = FStar_Syntax_Subst.compress t  in
                 uu____4589.FStar_Syntax_Syntax.n  in
               match uu____4588 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4593 -> false  in
             let uu____4594 = cur_goal ()  in
             bind uu____4594
               (fun goal  ->
                  let uu____4600 =
                    let uu____4609 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4609 tm  in
                  bind uu____4600
                    (fun uu____4624  ->
                       match uu____4624 with
                       | (tm1,t,guard) ->
                           let uu____4636 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4636 with
                            | (bs,comp) ->
                                let uu____4669 = lemma_or_sq comp  in
                                (match uu____4669 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4688 =
                                       FStar_List.fold_left
                                         (fun uu____4736  ->
                                            fun uu____4737  ->
                                              match (uu____4736, uu____4737)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4850 =
                                                    is_unit_t b_t  in
                                                  if uu____4850
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4888 =
                                                       let uu____4901 =
                                                         let uu____4902 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4902.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4905 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4901
                                                         uu____4905 b_t
                                                        in
                                                     match uu____4888 with
                                                     | (u,uu____4923,g_u) ->
                                                         let uu____4937 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4937,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4688 with
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
                                          let uu____5016 =
                                            let uu____5019 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____5020 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____5021 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____5019 uu____5020
                                              uu____5021
                                             in
                                          bind uu____5016
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____5029 =
                                                   let uu____5030 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____5030 tm1  in
                                                 let uu____5031 =
                                                   let uu____5032 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5033 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____5032 uu____5033
                                                    in
                                                 let uu____5034 =
                                                   let uu____5035 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5036 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____5035 uu____5036
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____5029 uu____5031
                                                   uu____5034
                                               else
                                                 (let uu____5038 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____5038
                                                    (fun uu____5043  ->
                                                       let uu____5044 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____5044
                                                         (fun uu____5052  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____5077
                                                                  =
                                                                  let uu____5080
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____5080
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____5077
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
                                                                   let uu____5115
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5115)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5131
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5131
                                                              with
                                                              | (hd1,uu____5149)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5175)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5192
                                                                    -> false)
                                                               in
                                                            let uu____5193 =
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
                                                                    let uu____5223
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5223
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5245)
                                                                    ->
                                                                    let uu____5270
                                                                    =
                                                                    let uu____5271
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5271.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5270
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5279)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___388_5299
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___388_5299.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___388_5299.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___388_5299.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5302
                                                                    ->
                                                                    let env =
                                                                    let uu___389_5304
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___389_5304.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5306
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5306
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
                                                                    let uu____5309
                                                                    =
                                                                    let uu____5316
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5316
                                                                    term1  in
                                                                    match uu____5309
                                                                    with
                                                                    | 
                                                                    (uu____5317,uu____5318,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5320
                                                                    =
                                                                    let uu____5323
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5323
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5320
                                                                    (fun
                                                                    uu____5327
                                                                     ->
                                                                    ret []))))
                                                               in
                                                            bind uu____5193
                                                              (fun sub_goals 
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
                                                                    let uu____5389
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5389
                                                                    then
                                                                    let uu____5392
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5392
                                                                    else
                                                                    filter' f
                                                                    xs1
                                                                    in
                                                                 let sub_goals2
                                                                   =
                                                                   filter'
                                                                    (fun g 
                                                                    ->
                                                                    fun goals
                                                                     ->
                                                                    let uu____5406
                                                                    =
                                                                    let uu____5407
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5407
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5406)
                                                                    sub_goals1
                                                                    in
                                                                 let uu____5408
                                                                   =
                                                                   let uu____5411
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5411
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5408
                                                                   (fun
                                                                    uu____5414
                                                                     ->
                                                                    let uu____5415
                                                                    =
                                                                    let uu____5418
                                                                    =
                                                                    let uu____5419
                                                                    =
                                                                    let uu____5420
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5421
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5420
                                                                    uu____5421
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5419
                                                                     in
                                                                    if
                                                                    uu____5418
                                                                    then
                                                                    let uu____5424
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5424
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5415
                                                                    (fun
                                                                    uu____5427
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2)))))))))))))
         in
      focus uu____4571  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4568
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5449 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5449 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5459::(e1,uu____5461)::(e2,uu____5463)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5524 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5548 = destruct_eq' typ  in
    match uu____5548 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5578 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5578 with
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
        let uu____5640 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5640 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5688 = aux e'  in
               FStar_Util.map_opt uu____5688
                 (fun uu____5712  ->
                    match uu____5712 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5733 = aux e  in
      FStar_Util.map_opt uu____5733
        (fun uu____5757  ->
           match uu____5757 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5824 =
            let uu____5833 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5833  in
          FStar_Util.map_opt uu____5824
            (fun uu____5848  ->
               match uu____5848 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___390_5867 = bv  in
                     let uu____5868 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___390_5867.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___390_5867.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5868
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___391_5876 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5877 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5886 =
                       let uu____5889 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5889  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___391_5876.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5877;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5886;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___391_5876.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___391_5876.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___391_5876.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___392_5890 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___392_5890.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___392_5890.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___392_5890.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5900 =
      let uu____5903 = cur_goal ()  in
      bind uu____5903
        (fun goal  ->
           let uu____5911 = h  in
           match uu____5911 with
           | (bv,uu____5915) ->
               mlog
                 (fun uu____5923  ->
                    let uu____5924 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5925 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5924
                      uu____5925)
                 (fun uu____5928  ->
                    let uu____5929 =
                      let uu____5938 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5938  in
                    match uu____5929 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5959 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5959 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5974 =
                               let uu____5975 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5975.FStar_Syntax_Syntax.n  in
                             (match uu____5974 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___393_5992 = bv1  in
                                    let uu____5993 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___393_5992.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___393_5992.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5993
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___394_6001 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6002 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6011 =
                                      let uu____6014 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6014
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___394_6001.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6002;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6011;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___394_6001.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___394_6001.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___394_6001.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___395_6017 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___395_6017.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___395_6017.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___395_6017.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6018 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6019 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5900
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6044 =
        let uu____6047 = cur_goal ()  in
        bind uu____6047
          (fun goal  ->
             let uu____6058 = b  in
             match uu____6058 with
             | (bv,uu____6062) ->
                 let bv' =
                   let uu____6068 =
                     let uu___396_6069 = bv  in
                     let uu____6070 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6070;
                       FStar_Syntax_Syntax.index =
                         (uu___396_6069.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___396_6069.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6068  in
                 let s1 =
                   let uu____6074 =
                     let uu____6075 =
                       let uu____6082 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6082)  in
                     FStar_Syntax_Syntax.NT uu____6075  in
                   [uu____6074]  in
                 let uu____6087 = subst_goal bv bv' s1 goal  in
                 (match uu____6087 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6044
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6106 =
      let uu____6109 = cur_goal ()  in
      bind uu____6109
        (fun goal  ->
           let uu____6118 = b  in
           match uu____6118 with
           | (bv,uu____6122) ->
               let uu____6127 =
                 let uu____6136 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6136  in
               (match uu____6127 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6157 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6157 with
                     | (ty,u) ->
                         let uu____6166 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6166
                           (fun uu____6184  ->
                              match uu____6184 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___397_6194 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___397_6194.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___397_6194.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6198 =
                                      let uu____6199 =
                                        let uu____6206 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6206)  in
                                      FStar_Syntax_Syntax.NT uu____6199  in
                                    [uu____6198]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___398_6218 = b1  in
                                         let uu____6219 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___398_6218.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___398_6218.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6219
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6226  ->
                                       let new_goal =
                                         let uu____6228 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6229 =
                                           let uu____6230 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6230
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6228 uu____6229
                                          in
                                       let uu____6231 = add_goals [new_goal]
                                          in
                                       bind uu____6231
                                         (fun uu____6236  ->
                                            let uu____6237 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6237
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6106
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6260 =
        let uu____6263 = cur_goal ()  in
        bind uu____6263
          (fun goal  ->
             let uu____6272 = b  in
             match uu____6272 with
             | (bv,uu____6276) ->
                 let uu____6281 =
                   let uu____6290 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6290  in
                 (match uu____6281 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6314 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6314
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___399_6319 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___399_6319.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___399_6319.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6321 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6321))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6260
  
let (revert : unit -> unit tac) =
  fun uu____6332  ->
    let uu____6335 = cur_goal ()  in
    bind uu____6335
      (fun goal  ->
         let uu____6341 =
           let uu____6348 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6348  in
         match uu____6341 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6364 =
                 let uu____6367 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6367  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6364
                in
             let uu____6382 = new_uvar "revert" env' typ'  in
             bind uu____6382
               (fun uu____6397  ->
                  match uu____6397 with
                  | (r,u_r) ->
                      let uu____6406 =
                        let uu____6409 =
                          let uu____6410 =
                            let uu____6411 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6411.FStar_Syntax_Syntax.pos  in
                          let uu____6414 =
                            let uu____6419 =
                              let uu____6420 =
                                let uu____6429 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6429  in
                              [uu____6420]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6419  in
                          uu____6414 FStar_Pervasives_Native.None uu____6410
                           in
                        set_solution goal uu____6409  in
                      bind uu____6406
                        (fun uu____6450  ->
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
      let uu____6462 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6462
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6477 = cur_goal ()  in
    bind uu____6477
      (fun goal  ->
         mlog
           (fun uu____6485  ->
              let uu____6486 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6487 =
                let uu____6488 =
                  let uu____6489 =
                    let uu____6498 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6498  in
                  FStar_All.pipe_right uu____6489 FStar_List.length  in
                FStar_All.pipe_right uu____6488 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6486 uu____6487)
           (fun uu____6515  ->
              let uu____6516 =
                let uu____6525 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6525  in
              match uu____6516 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6564 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6564
                        then
                          let uu____6567 =
                            let uu____6568 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6568
                             in
                          fail uu____6567
                        else check1 bvs2
                     in
                  let uu____6570 =
                    let uu____6571 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6571  in
                  if uu____6570
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6575 = check1 bvs  in
                     bind uu____6575
                       (fun uu____6581  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6583 =
                            let uu____6590 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6590  in
                          bind uu____6583
                            (fun uu____6599  ->
                               match uu____6599 with
                               | (ut,uvar_ut) ->
                                   let uu____6608 = set_solution goal ut  in
                                   bind uu____6608
                                     (fun uu____6613  ->
                                        let uu____6614 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6614))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6621  ->
    let uu____6624 = cur_goal ()  in
    bind uu____6624
      (fun goal  ->
         let uu____6630 =
           let uu____6637 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6637  in
         match uu____6630 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6645) ->
             let uu____6650 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6650)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6660 = cur_goal ()  in
    bind uu____6660
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6670 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6670  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6673  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6683 = cur_goal ()  in
    bind uu____6683
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6693 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6693  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6696  -> add_goals [g']))
  
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
            let uu____6736 = FStar_Syntax_Subst.compress t  in
            uu____6736.FStar_Syntax_Syntax.n  in
          let uu____6739 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___403_6745 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___403_6745.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___403_6745.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6739
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6761 =
                   let uu____6762 = FStar_Syntax_Subst.compress t1  in
                   uu____6762.FStar_Syntax_Syntax.n  in
                 match uu____6761 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6793 = ff hd1  in
                     bind uu____6793
                       (fun hd2  ->
                          let fa uu____6819 =
                            match uu____6819 with
                            | (a,q) ->
                                let uu____6840 = ff a  in
                                bind uu____6840 (fun a1  -> ret (a1, q))
                             in
                          let uu____6859 = mapM fa args  in
                          bind uu____6859
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6941 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6941 with
                      | (bs1,t') ->
                          let uu____6950 =
                            let uu____6953 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6953 t'  in
                          bind uu____6950
                            (fun t''  ->
                               let uu____6957 =
                                 let uu____6958 =
                                   let uu____6977 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6986 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6977, uu____6986, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6958  in
                               ret uu____6957))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7061 = ff hd1  in
                     bind uu____7061
                       (fun hd2  ->
                          let ffb br =
                            let uu____7076 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7076 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7108 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7108  in
                                let uu____7109 = ff1 e  in
                                bind uu____7109
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7124 = mapM ffb brs  in
                          bind uu____7124
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7168;
                          FStar_Syntax_Syntax.lbtyp = uu____7169;
                          FStar_Syntax_Syntax.lbeff = uu____7170;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7172;
                          FStar_Syntax_Syntax.lbpos = uu____7173;_}::[]),e)
                     ->
                     let lb =
                       let uu____7198 =
                         let uu____7199 = FStar_Syntax_Subst.compress t1  in
                         uu____7199.FStar_Syntax_Syntax.n  in
                       match uu____7198 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7203) -> lb
                       | uu____7216 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7225 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7225
                         (fun def1  ->
                            ret
                              (let uu___400_7231 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___400_7231.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___400_7231.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___400_7231.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___400_7231.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___400_7231.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___400_7231.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7232 = fflb lb  in
                     bind uu____7232
                       (fun lb1  ->
                          let uu____7242 =
                            let uu____7247 =
                              let uu____7248 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7248]  in
                            FStar_Syntax_Subst.open_term uu____7247 e  in
                          match uu____7242 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7278 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7278  in
                              let uu____7279 = ff1 e1  in
                              bind uu____7279
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7320 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7320
                         (fun def  ->
                            ret
                              (let uu___401_7326 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___401_7326.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___401_7326.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___401_7326.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___401_7326.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___401_7326.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___401_7326.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7327 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7327 with
                      | (lbs1,e1) ->
                          let uu____7342 = mapM fflb lbs1  in
                          bind uu____7342
                            (fun lbs2  ->
                               let uu____7354 = ff e1  in
                               bind uu____7354
                                 (fun e2  ->
                                    let uu____7362 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7362 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7430 = ff t2  in
                     bind uu____7430
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7461 = ff t2  in
                     bind uu____7461
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7468 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___402_7475 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___402_7475.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___402_7475.FStar_Syntax_Syntax.vars)
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
            let uu____7512 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___404_7521 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___404_7521.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___404_7521.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___404_7521.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___404_7521.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___404_7521.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___404_7521.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___404_7521.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___404_7521.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___404_7521.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___404_7521.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___404_7521.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___404_7521.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___404_7521.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___404_7521.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___404_7521.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___404_7521.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___404_7521.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___404_7521.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___404_7521.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___404_7521.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___404_7521.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___404_7521.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___404_7521.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___404_7521.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___404_7521.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___404_7521.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___404_7521.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___404_7521.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___404_7521.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___404_7521.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___404_7521.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___404_7521.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___404_7521.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___404_7521.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___404_7521.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___404_7521.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___404_7521.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___404_7521.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___404_7521.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___404_7521.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___404_7521.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7512 with
            | (t1,lcomp,g) ->
                let uu____7527 =
                  (let uu____7530 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7530) ||
                    (let uu____7532 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7532)
                   in
                if uu____7527
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7540 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7540
                       (fun uu____7556  ->
                          match uu____7556 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7569  ->
                                    let uu____7570 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7571 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7570 uu____7571);
                               (let uu____7572 =
                                  let uu____7575 =
                                    let uu____7576 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7576 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7575
                                    opts
                                   in
                                bind uu____7572
                                  (fun uu____7579  ->
                                     let uu____7580 =
                                       bind tau
                                         (fun uu____7586  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7592  ->
                                                 let uu____7593 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7594 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7593 uu____7594);
                                            ret ut1)
                                        in
                                     focus uu____7580))))
                      in
                   let uu____7595 = trytac' rewrite_eq  in
                   bind uu____7595
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
          let uu____7793 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7793
            (fun t1  ->
               let uu____7801 =
                 f env
                   (let uu___407_7810 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___407_7810.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___407_7810.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7801
                 (fun uu____7826  ->
                    match uu____7826 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7849 =
                               let uu____7850 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7850.FStar_Syntax_Syntax.n  in
                             match uu____7849 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7887 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7887
                                   (fun uu____7912  ->
                                      match uu____7912 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7928 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7928
                                            (fun uu____7955  ->
                                               match uu____7955 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___405_7985 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___405_7985.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___405_7985.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8027 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8027 with
                                  | (bs1,t') ->
                                      let uu____8042 =
                                        let uu____8049 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8049 ctrl1 t'
                                         in
                                      bind uu____8042
                                        (fun uu____8067  ->
                                           match uu____8067 with
                                           | (t'',ctrl2) ->
                                               let uu____8082 =
                                                 let uu____8089 =
                                                   let uu___406_8092 = t4  in
                                                   let uu____8095 =
                                                     let uu____8096 =
                                                       let uu____8115 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8124 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8115,
                                                         uu____8124, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8096
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8095;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___406_8092.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___406_8092.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8089, ctrl2)  in
                                               ret uu____8082))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8177 -> ret (t3, ctrl1))))

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
              let uu____8224 = ctrl_tac_fold f env ctrl t  in
              bind uu____8224
                (fun uu____8248  ->
                   match uu____8248 with
                   | (t1,ctrl1) ->
                       let uu____8263 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8263
                         (fun uu____8290  ->
                            match uu____8290 with
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
              let uu____8374 =
                let uu____8381 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8381
                  (fun uu____8390  ->
                     let uu____8391 = ctrl t1  in
                     bind uu____8391
                       (fun res  ->
                          let uu____8414 = trivial ()  in
                          bind uu____8414 (fun uu____8422  -> ret res)))
                 in
              bind uu____8374
                (fun uu____8438  ->
                   match uu____8438 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8462 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___408_8471 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___408_8471.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___408_8471.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___408_8471.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___408_8471.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___408_8471.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___408_8471.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___408_8471.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___408_8471.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___408_8471.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___408_8471.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___408_8471.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___408_8471.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___408_8471.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___408_8471.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___408_8471.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___408_8471.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___408_8471.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___408_8471.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___408_8471.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___408_8471.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___408_8471.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___408_8471.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___408_8471.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___408_8471.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___408_8471.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___408_8471.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___408_8471.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___408_8471.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___408_8471.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___408_8471.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___408_8471.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___408_8471.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___408_8471.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___408_8471.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___408_8471.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___408_8471.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___408_8471.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___408_8471.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___408_8471.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___408_8471.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___408_8471.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8462 with
                          | (t2,lcomp,g) ->
                              let uu____8481 =
                                (let uu____8484 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8484) ||
                                  (let uu____8486 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8486)
                                 in
                              if uu____8481
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8499 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8499
                                   (fun uu____8519  ->
                                      match uu____8519 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8536  ->
                                                let uu____8537 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8538 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8537 uu____8538);
                                           (let uu____8539 =
                                              let uu____8542 =
                                                let uu____8543 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8543 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8542 opts
                                               in
                                            bind uu____8539
                                              (fun uu____8550  ->
                                                 let uu____8551 =
                                                   bind rewriter
                                                     (fun uu____8565  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8571  ->
                                                             let uu____8572 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8573 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8572
                                                               uu____8573);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8551)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8614 =
        bind get
          (fun ps  ->
             let uu____8624 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8624 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8661  ->
                       let uu____8662 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8662);
                  bind dismiss_all
                    (fun uu____8665  ->
                       let uu____8666 =
                         let uu____8673 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8673
                           keepGoing gt1
                          in
                       bind uu____8666
                         (fun uu____8685  ->
                            match uu____8685 with
                            | (gt',uu____8693) ->
                                (log ps
                                   (fun uu____8697  ->
                                      let uu____8698 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8698);
                                 (let uu____8699 = push_goals gs  in
                                  bind uu____8699
                                    (fun uu____8704  ->
                                       let uu____8705 =
                                         let uu____8708 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8708]  in
                                       add_goals uu____8705)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8614
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8731 =
        bind get
          (fun ps  ->
             let uu____8741 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8741 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8778  ->
                       let uu____8779 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8779);
                  bind dismiss_all
                    (fun uu____8782  ->
                       let uu____8783 =
                         let uu____8786 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8786 gt1
                          in
                       bind uu____8783
                         (fun gt'  ->
                            log ps
                              (fun uu____8794  ->
                                 let uu____8795 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8795);
                            (let uu____8796 = push_goals gs  in
                             bind uu____8796
                               (fun uu____8801  ->
                                  let uu____8802 =
                                    let uu____8805 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8805]  in
                                  add_goals uu____8802))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8731
  
let (trefl : unit -> unit tac) =
  fun uu____8816  ->
    let uu____8819 =
      let uu____8822 = cur_goal ()  in
      bind uu____8822
        (fun g  ->
           let uu____8840 =
             let uu____8845 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8845  in
           match uu____8840 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8853 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8853 with
                | (hd1,args) ->
                    let uu____8892 =
                      let uu____8905 =
                        let uu____8906 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8906.FStar_Syntax_Syntax.n  in
                      (uu____8905, args)  in
                    (match uu____8892 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8920::(l,uu____8922)::(r,uu____8924)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8971 =
                           let uu____8974 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8974 l r  in
                         bind uu____8971
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8981 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8981 l
                                    in
                                 let r1 =
                                   let uu____8983 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8983 r
                                    in
                                 let uu____8984 =
                                   let uu____8987 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8987 l1 r1  in
                                 bind uu____8984
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8993 =
                                           let uu____8994 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8994 l1  in
                                         let uu____8995 =
                                           let uu____8996 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8996 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8993 uu____8995))))
                     | (hd2,uu____8998) ->
                         let uu____9015 =
                           let uu____9016 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9016 t  in
                         fail1 "trefl: not an equality (%s)" uu____9015))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8819
  
let (dup : unit -> unit tac) =
  fun uu____9029  ->
    let uu____9032 = cur_goal ()  in
    bind uu____9032
      (fun g  ->
         let uu____9038 =
           let uu____9045 = FStar_Tactics_Types.goal_env g  in
           let uu____9046 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9045 uu____9046  in
         bind uu____9038
           (fun uu____9055  ->
              match uu____9055 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___409_9065 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___409_9065.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___409_9065.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___409_9065.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9068  ->
                       let uu____9069 =
                         let uu____9072 = FStar_Tactics_Types.goal_env g  in
                         let uu____9073 =
                           let uu____9074 =
                             let uu____9075 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9076 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9075
                               uu____9076
                              in
                           let uu____9077 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9078 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9074 uu____9077 u
                             uu____9078
                            in
                         add_irrelevant_goal "dup equation" uu____9072
                           uu____9073 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9069
                         (fun uu____9081  ->
                            let uu____9082 = add_goals [g']  in
                            bind uu____9082 (fun uu____9086  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9093  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___410_9110 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___410_9110.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___410_9110.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___410_9110.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___410_9110.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___410_9110.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___410_9110.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___410_9110.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___410_9110.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___410_9110.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___410_9110.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___410_9110.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9111 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9120  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___411_9133 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___411_9133.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___411_9133.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___411_9133.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___411_9133.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___411_9133.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___411_9133.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___411_9133.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___411_9133.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___411_9133.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___411_9133.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___411_9133.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9140  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9147 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9167 =
      let uu____9174 = cur_goal ()  in
      bind uu____9174
        (fun g  ->
           let uu____9184 =
             let uu____9193 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9193 t  in
           bind uu____9184
             (fun uu____9221  ->
                match uu____9221 with
                | (t1,typ,guard) ->
                    let uu____9237 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9237 with
                     | (hd1,args) ->
                         let uu____9286 =
                           let uu____9301 =
                             let uu____9302 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9302.FStar_Syntax_Syntax.n  in
                           (uu____9301, args)  in
                         (match uu____9286 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9323)::(q,uu____9325)::[]) when
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
                                let uu____9379 =
                                  let uu____9380 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9380
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9379
                                 in
                              let g2 =
                                let uu____9382 =
                                  let uu____9383 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9383
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9382
                                 in
                              bind __dismiss
                                (fun uu____9390  ->
                                   let uu____9391 = add_goals [g1; g2]  in
                                   bind uu____9391
                                     (fun uu____9400  ->
                                        let uu____9401 =
                                          let uu____9406 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9407 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9406, uu____9407)  in
                                        ret uu____9401))
                          | uu____9412 ->
                              let uu____9427 =
                                let uu____9428 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9428 typ  in
                              fail1 "Not a disjunction: %s" uu____9427))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9167
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9458 =
      let uu____9461 = cur_goal ()  in
      bind uu____9461
        (fun g  ->
           FStar_Options.push ();
           (let uu____9474 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9474);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___412_9481 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___412_9481.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___412_9481.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___412_9481.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9458
  
let (top_env : unit -> env tac) =
  fun uu____9493  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9506  ->
    let uu____9509 = cur_goal ()  in
    bind uu____9509
      (fun g  ->
         let uu____9515 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9515)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9524  ->
    let uu____9527 = cur_goal ()  in
    bind uu____9527
      (fun g  ->
         let uu____9533 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9533)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9542  ->
    let uu____9545 = cur_goal ()  in
    bind uu____9545
      (fun g  ->
         let uu____9551 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9551)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9560  ->
    let uu____9563 = cur_env ()  in
    bind uu____9563
      (fun e  ->
         let uu____9569 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____9569)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9584 =
        mlog
          (fun uu____9589  ->
             let uu____9590 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9590)
          (fun uu____9593  ->
             let uu____9594 = cur_goal ()  in
             bind uu____9594
               (fun goal  ->
                  let env =
                    let uu____9602 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9602 ty  in
                  let uu____9603 = __tc env tm  in
                  bind uu____9603
                    (fun uu____9622  ->
                       match uu____9622 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9636  ->
                                let uu____9637 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9637)
                             (fun uu____9639  ->
                                mlog
                                  (fun uu____9642  ->
                                     let uu____9643 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9643)
                                  (fun uu____9646  ->
                                     let uu____9647 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9647
                                       (fun uu____9651  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9584
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9674 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9680 =
              let uu____9687 =
                let uu____9688 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9688
                 in
              new_uvar "uvar_env.2" env uu____9687  in
            bind uu____9680
              (fun uu____9704  ->
                 match uu____9704 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9674
        (fun typ  ->
           let uu____9716 = new_uvar "uvar_env" env typ  in
           bind uu____9716
             (fun uu____9730  -> match uu____9730 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9748 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9767 -> g.FStar_Tactics_Types.opts
             | uu____9770 -> FStar_Options.peek ()  in
           let uu____9773 = FStar_Syntax_Util.head_and_args t  in
           match uu____9773 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9793);
                FStar_Syntax_Syntax.pos = uu____9794;
                FStar_Syntax_Syntax.vars = uu____9795;_},uu____9796)
               ->
               let env1 =
                 let uu___413_9838 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___413_9838.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___413_9838.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___413_9838.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___413_9838.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___413_9838.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___413_9838.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___413_9838.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___413_9838.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___413_9838.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___413_9838.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___413_9838.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___413_9838.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___413_9838.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___413_9838.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___413_9838.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___413_9838.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___413_9838.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___413_9838.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___413_9838.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___413_9838.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___413_9838.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___413_9838.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___413_9838.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___413_9838.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___413_9838.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___413_9838.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___413_9838.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___413_9838.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___413_9838.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___413_9838.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___413_9838.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___413_9838.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___413_9838.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___413_9838.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___413_9838.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___413_9838.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___413_9838.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___413_9838.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___413_9838.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___413_9838.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___413_9838.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9840 =
                 let uu____9843 = bnorm_goal g  in [uu____9843]  in
               add_goals uu____9840
           | uu____9844 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9748
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9893 = if b then t2 else ret false  in
             bind uu____9893 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9904 = trytac comp  in
      bind uu____9904
        (fun uu___350_9912  ->
           match uu___350_9912 with
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
        let uu____9938 =
          bind get
            (fun ps  ->
               let uu____9944 = __tc e t1  in
               bind uu____9944
                 (fun uu____9964  ->
                    match uu____9964 with
                    | (t11,ty1,g1) ->
                        let uu____9976 = __tc e t2  in
                        bind uu____9976
                          (fun uu____9996  ->
                             match uu____9996 with
                             | (t21,ty2,g2) ->
                                 let uu____10008 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10008
                                   (fun uu____10013  ->
                                      let uu____10014 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10014
                                        (fun uu____10020  ->
                                           let uu____10021 =
                                             do_unify e ty1 ty2  in
                                           let uu____10024 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10021 uu____10024)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9938
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10057  ->
             let uu____10058 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10058
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
        (fun uu____10079  ->
           let uu____10080 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10080)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10090 =
      mlog
        (fun uu____10095  ->
           let uu____10096 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10096)
        (fun uu____10099  ->
           let uu____10100 = cur_goal ()  in
           bind uu____10100
             (fun g  ->
                let uu____10106 =
                  let uu____10115 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10115 ty  in
                bind uu____10106
                  (fun uu____10127  ->
                     match uu____10127 with
                     | (ty1,uu____10137,guard) ->
                         let uu____10139 =
                           let uu____10142 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10142 guard  in
                         bind uu____10139
                           (fun uu____10145  ->
                              let uu____10146 =
                                let uu____10149 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10150 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10149 uu____10150 ty1  in
                              bind uu____10146
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10156 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10156
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
                                        let uu____10162 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10163 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10162
                                          uu____10163
                                         in
                                      let nty =
                                        let uu____10165 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10165 ty1  in
                                      let uu____10166 =
                                        let uu____10169 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10169 ng nty  in
                                      bind uu____10166
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10175 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10175
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10090
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10238 =
      let uu____10247 = cur_goal ()  in
      bind uu____10247
        (fun g  ->
           let uu____10259 =
             let uu____10268 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10268 s_tm  in
           bind uu____10259
             (fun uu____10286  ->
                match uu____10286 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10304 =
                      let uu____10307 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10307 guard  in
                    bind uu____10304
                      (fun uu____10319  ->
                         let uu____10320 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10320 with
                         | (h,args) ->
                             let uu____10365 =
                               let uu____10372 =
                                 let uu____10373 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10373.FStar_Syntax_Syntax.n  in
                               match uu____10372 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10388;
                                      FStar_Syntax_Syntax.vars = uu____10389;_},us)
                                   -> ret (fv, us)
                               | uu____10399 -> fail "type is not an fv"  in
                             bind uu____10365
                               (fun uu____10419  ->
                                  match uu____10419 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10435 =
                                        let uu____10438 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10438 t_lid
                                         in
                                      (match uu____10435 with
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
                                                  (fun uu____10487  ->
                                                     let uu____10488 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10488 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10503 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10531
                                                                  =
                                                                  let uu____10534
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10534
                                                                    c_lid
                                                                   in
                                                                match uu____10531
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
                                                                    uu____10604
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
                                                                    let uu____10609
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10609
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10632
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10632
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10675
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10675
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____10748
                                                                    =
                                                                    let uu____10749
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____10749
                                                                     in
                                                                    failwhen
                                                                    uu____10748
                                                                    "not total?"
                                                                    (fun
                                                                    uu____10766
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
                                                                    uu___351_10782
                                                                    =
                                                                    match uu___351_10782
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____10785)
                                                                    -> true
                                                                    | 
                                                                    uu____10786
                                                                    -> false
                                                                     in
                                                                    let uu____10789
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____10789
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
                                                                    uu____10922
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
                                                                    uu____10984
                                                                     ->
                                                                    match uu____10984
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11004),
                                                                    (t,uu____11006))
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
                                                                    uu____11074
                                                                     ->
                                                                    match uu____11074
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11100),
                                                                    (t,uu____11102))
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
                                                                    uu____11157
                                                                     ->
                                                                    match uu____11157
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
                                                                    let uu____11207
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___414_11224
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___414_11224.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11207
                                                                    with
                                                                    | 
                                                                    (uu____11237,uu____11238,uu____11239,pat_t,uu____11241,uu____11242)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11248
                                                                    =
                                                                    let uu____11249
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11249
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11248
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11253
                                                                    =
                                                                    let uu____11262
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11262]
                                                                     in
                                                                    let uu____11281
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11253
                                                                    uu____11281
                                                                     in
                                                                    let nty =
                                                                    let uu____11287
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11287
                                                                     in
                                                                    let uu____11290
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11290
                                                                    (fun
                                                                    uu____11319
                                                                     ->
                                                                    match uu____11319
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
                                                                    let uu____11345
                                                                    =
                                                                    let uu____11356
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11356]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11345
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11392
                                                                    =
                                                                    let uu____11403
                                                                    =
                                                                    let uu____11408
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11408)
                                                                     in
                                                                    (g', br,
                                                                    uu____11403)
                                                                     in
                                                                    ret
                                                                    uu____11392))))))
                                                                    | 
                                                                    uu____11429
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10503
                                                           (fun goal_brs  ->
                                                              let uu____11478
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11478
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
                                                                  let uu____11551
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11551
                                                                    (
                                                                    fun
                                                                    uu____11562
                                                                     ->
                                                                    let uu____11563
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11563
                                                                    (fun
                                                                    uu____11573
                                                                     ->
                                                                    ret infos))))
                                            | uu____11580 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10238
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11625::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11653 = init xs  in x :: uu____11653
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11665 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____11673) -> inspect t3
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
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____11774, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____11769  in
               FStar_All.pipe_left ret uu____11768)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____11793,uu____11794) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____11846 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____11846 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____11887 =
                      let uu____11888 =
                        let uu____11893 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____11893)  in
                      FStar_Reflection_Data.Tv_Abs uu____11888  in
                    FStar_All.pipe_left ret uu____11887))
      | FStar_Syntax_Syntax.Tm_type uu____11896 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____11920 ->
          let uu____11935 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____11935 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____11965 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____11965 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12018 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
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
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
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
            | FStar_Syntax_Syntax.Pat_dot_term (bv,t4) ->
                FStar_Reflection_Data.Pat_Dot_Term (bv, t4)
             in
          let brs1 = FStar_List.map FStar_Syntax_Subst.open_branch brs  in
          let brs2 =
            FStar_List.map
              (fun uu___352_12407  ->
                 match uu___352_12407 with
                 | (pat,uu____12429,t4) ->
                     let uu____12447 = inspect_pat pat  in (uu____12447, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12456 ->
          ((let uu____12458 =
              let uu____12463 =
                let uu____12464 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____12465 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12464 uu____12465
                 in
              (FStar_Errors.Warning_CantInspect, uu____12463)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____12458);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11665
  
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
  