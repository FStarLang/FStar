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
      try (fun uu___350_154  -> match () with | () -> t.tac_f p) ()
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
                 let uu___351_1034 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___351_1034.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___351_1034.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___351_1034.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___351_1034.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___351_1034.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___351_1034.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___351_1034.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___351_1034.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___351_1034.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___351_1034.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___351_1034.FStar_Tactics_Types.tac_verb_dbg)
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
         try
           (fun uu___353_1119  ->
              match () with
              | () -> let uu____1124 = trytac t  in run uu____1124 ps) ()
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
           (fun uu___355_1236  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1241 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1241
                    then
                      let uu____1242 = FStar_Util.string_of_bool res  in
                      let uu____1243 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1244 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1242
                        uu____1243 uu____1244
                    else ());
                   ret res)) ()
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
         let uu___356_1277 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___356_1277.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___356_1277.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___356_1277.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___357_1280 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___357_1280.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___357_1280.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___357_1280.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___357_1280.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___357_1280.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___357_1280.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___357_1280.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___357_1280.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___357_1280.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___357_1280.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___357_1280.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___358_1326 = ps  in
         let uu____1327 =
           FStar_List.filter
             (fun g  ->
                let uu____1333 = check_goal_solved g  in
                FStar_Option.isNone uu____1333) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___358_1326.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___358_1326.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___358_1326.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1327;
           FStar_Tactics_Types.smt_goals =
             (uu___358_1326.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___358_1326.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___358_1326.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___358_1326.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___358_1326.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___358_1326.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___358_1326.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___358_1326.FStar_Tactics_Types.tac_verb_dbg)
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
         let uu___359_1381 = p  in
         let uu____1382 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___359_1381.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___359_1381.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___359_1381.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1382;
           FStar_Tactics_Types.smt_goals =
             (uu___359_1381.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___359_1381.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___359_1381.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___359_1381.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___359_1381.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___359_1381.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___359_1381.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___359_1381.FStar_Tactics_Types.tac_verb_dbg)
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
         (let uu___360_1472 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___360_1472.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___360_1472.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___360_1472.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___360_1472.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___360_1472.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___360_1472.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___360_1472.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___360_1472.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___360_1472.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___360_1472.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___360_1472.FStar_Tactics_Types.tac_verb_dbg)
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
           (let uu___361_1627 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___361_1627.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___361_1627.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___361_1627.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___361_1627.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___361_1627.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___361_1627.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___361_1627.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___361_1627.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___361_1627.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___361_1627.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___361_1627.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___362_1647 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___362_1647.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___362_1647.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___362_1647.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___362_1647.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___362_1647.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___362_1647.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___362_1647.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___362_1647.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___362_1647.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___362_1647.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___362_1647.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___363_1667 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___363_1667.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___363_1667.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___363_1667.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___363_1667.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___363_1667.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___363_1667.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___363_1667.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___363_1667.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___363_1667.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___363_1667.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___363_1667.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___364_1687 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___364_1687.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___364_1687.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___364_1687.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___364_1687.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___364_1687.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___364_1687.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___364_1687.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___364_1687.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___364_1687.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___364_1687.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___364_1687.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1698  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___365_1712 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___365_1712.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___365_1712.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___365_1712.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___365_1712.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___365_1712.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___365_1712.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___365_1712.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___365_1712.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___365_1712.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___365_1712.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___365_1712.FStar_Tactics_Types.tac_verb_dbg)
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
           let uu___366_1934 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___366_1934.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___366_1934.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___366_1934.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___366_1934.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___366_1934.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___366_1934.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___366_1934.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___366_1934.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___366_1934.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___366_1934.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___366_1934.FStar_Tactics_Types.tac_verb_dbg)
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
                  let uu___367_2099 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___367_2099.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___367_2099.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___367_2099.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___367_2099.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___367_2099.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___367_2099.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___367_2099.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___367_2099.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___367_2099.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___367_2099.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___367_2099.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___367_2099.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___367_2099.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___367_2099.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___367_2099.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___367_2099.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___367_2099.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___367_2099.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___367_2099.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___367_2099.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___367_2099.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___367_2099.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___367_2099.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___367_2099.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___367_2099.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___367_2099.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___367_2099.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___367_2099.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___367_2099.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___367_2099.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___367_2099.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___367_2099.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___367_2099.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___367_2099.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___367_2099.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___367_2099.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___367_2099.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___367_2099.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___367_2099.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___367_2099.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___367_2099.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___369_2110  ->
                     match () with
                     | () ->
                         let uu____2119 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2119) ()
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
           (let uu___370_2207 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_2207.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_2207.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_2207.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_2207.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___370_2207.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___370_2207.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_2207.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_2207.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_2207.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___370_2207.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_2207.FStar_Tactics_Types.tac_verb_dbg)
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
    (fun uu___341_2264  ->
       match uu___341_2264 with
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
                                   let uu___371_2313 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___371_2313.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___371_2313.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___371_2313.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2314 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2314
                              (fun goal  ->
                                 let goal1 =
                                   let uu___372_2321 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___372_2321.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___372_2321.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___372_2321.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               (fun uu___374_2326  ->
                                  match () with
                                  | () ->
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
                                             fail1
                                               "Forcing the guard failed %s)"
                                               reason)
                                      else ret ()) ()
                             with
                             | uu___373_2342 ->
                                 mlog
                                   (fun uu____2347  ->
                                      let uu____2348 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2348)
                                   (fun uu____2350  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2360 =
      let uu____2363 = cur_goal ()  in
      bind uu____2363
        (fun goal  ->
           let uu____2369 =
             let uu____2378 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2378 t  in
           bind uu____2369
             (fun uu____2389  ->
                match uu____2389 with
                | (uu____2398,typ,uu____2400) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2360
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2429 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2429 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2440  ->
    let uu____2443 = cur_goal ()  in
    bind uu____2443
      (fun goal  ->
         let uu____2449 =
           let uu____2450 = FStar_Tactics_Types.goal_env goal  in
           let uu____2451 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2450 uu____2451  in
         if uu____2449
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2455 =
              let uu____2456 = FStar_Tactics_Types.goal_env goal  in
              let uu____2457 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2456 uu____2457  in
            fail1 "Not a trivial goal: %s" uu____2455))
  
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
          let uu____2486 =
            let uu____2487 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2487.FStar_TypeChecker_Env.guard_f  in
          match uu____2486 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2495 = istrivial e f  in
              if uu____2495
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2503 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2503
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___375_2513 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___375_2513.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___375_2513.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___375_2513.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2520  ->
    let uu____2523 = cur_goal ()  in
    bind uu____2523
      (fun g  ->
         let uu____2529 = is_irrelevant g  in
         if uu____2529
         then bind __dismiss (fun uu____2533  -> add_smt_goals [g])
         else
           (let uu____2535 =
              let uu____2536 = FStar_Tactics_Types.goal_env g  in
              let uu____2537 = FStar_Tactics_Types.goal_type g  in
              tts uu____2536 uu____2537  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2535))
  
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
             let uu____2586 =
               try
                 (fun uu___380_2609  ->
                    match () with
                    | () ->
                        let uu____2620 =
                          let uu____2629 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2629
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2620) ()
               with | uu___379_2639 -> fail "divide: not enough goals"  in
             bind uu____2586
               (fun uu____2675  ->
                  match uu____2675 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___376_2701 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___376_2701.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___376_2701.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___376_2701.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___376_2701.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___376_2701.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___376_2701.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___376_2701.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___376_2701.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___376_2701.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___376_2701.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2702 = set lp  in
                      bind uu____2702
                        (fun uu____2710  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___377_2726 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___377_2726.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___377_2726.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___377_2726.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___377_2726.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___377_2726.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___377_2726.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___377_2726.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___377_2726.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___377_2726.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___377_2726.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2727 = set rp  in
                                     bind uu____2727
                                       (fun uu____2735  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___378_2751 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___378_2751.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___378_2751.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2752 = set p'
                                                       in
                                                    bind uu____2752
                                                      (fun uu____2760  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2766 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2787 = divide FStar_BigInt.one f idtac  in
    bind uu____2787
      (fun uu____2800  -> match uu____2800 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2837::uu____2838 ->
             let uu____2841 =
               let uu____2850 = map tau  in
               divide FStar_BigInt.one tau uu____2850  in
             bind uu____2841
               (fun uu____2868  ->
                  match uu____2868 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2909 =
        bind t1
          (fun uu____2914  ->
             let uu____2915 = map t2  in
             bind uu____2915 (fun uu____2923  -> ret ()))
         in
      focus uu____2909
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2932  ->
    let uu____2935 =
      let uu____2938 = cur_goal ()  in
      bind uu____2938
        (fun goal  ->
           let uu____2947 =
             let uu____2954 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2954  in
           match uu____2947 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2963 =
                 let uu____2964 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2964  in
               if uu____2963
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2969 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2969 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2983 = new_uvar "intro" env' typ'  in
                  bind uu____2983
                    (fun uu____2999  ->
                       match uu____2999 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3023 = set_solution goal sol  in
                           bind uu____3023
                             (fun uu____3029  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3031 =
                                  let uu____3034 = bnorm_goal g  in
                                  replace_cur uu____3034  in
                                bind uu____3031 (fun uu____3036  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3041 =
                 let uu____3042 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3043 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3042 uu____3043  in
               fail1 "goal is not an arrow (%s)" uu____3041)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2935
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3058  ->
    let uu____3065 = cur_goal ()  in
    bind uu____3065
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3082 =
            let uu____3089 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3089  in
          match uu____3082 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3102 =
                let uu____3103 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3103  in
              if uu____3102
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3116 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3116
                    in
                 let bs =
                   let uu____3126 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3126; b]  in
                 let env' =
                   let uu____3152 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3152 bs  in
                 let uu____3153 =
                   let uu____3160 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3160  in
                 bind uu____3153
                   (fun uu____3179  ->
                      match uu____3179 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3193 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3196 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3193
                              FStar_Parser_Const.effect_Tot_lid uu____3196 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3214 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3214 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3236 =
                                   let uu____3237 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3237.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3236
                                  in
                               let uu____3250 = set_solution goal tm  in
                               bind uu____3250
                                 (fun uu____3259  ->
                                    let uu____3260 =
                                      let uu____3263 =
                                        bnorm_goal
                                          (let uu___381_3266 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___381_3266.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___381_3266.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___381_3266.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3263  in
                                    bind uu____3260
                                      (fun uu____3273  ->
                                         let uu____3274 =
                                           let uu____3279 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3279, b)  in
                                         ret uu____3274)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3288 =
                let uu____3289 = FStar_Tactics_Types.goal_env goal  in
                let uu____3290 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3289 uu____3290  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3288))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3308 = cur_goal ()  in
    bind uu____3308
      (fun goal  ->
         mlog
           (fun uu____3315  ->
              let uu____3316 =
                let uu____3317 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3317  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3316)
           (fun uu____3322  ->
              let steps =
                let uu____3326 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3326
                 in
              let t =
                let uu____3330 = FStar_Tactics_Types.goal_env goal  in
                let uu____3331 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3330 uu____3331  in
              let uu____3332 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3332))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3356 =
          mlog
            (fun uu____3361  ->
               let uu____3362 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3362)
            (fun uu____3364  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3370 -> g.FStar_Tactics_Types.opts
                      | uu____3373 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3378  ->
                         let uu____3379 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3379)
                      (fun uu____3382  ->
                         let uu____3383 = __tc e t  in
                         bind uu____3383
                           (fun uu____3404  ->
                              match uu____3404 with
                              | (t1,uu____3414,uu____3415) ->
                                  let steps =
                                    let uu____3419 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3419
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3356
  
let (refine_intro : unit -> unit tac) =
  fun uu____3433  ->
    let uu____3436 =
      let uu____3439 = cur_goal ()  in
      bind uu____3439
        (fun g  ->
           let uu____3446 =
             let uu____3457 = FStar_Tactics_Types.goal_env g  in
             let uu____3458 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3457 uu____3458
              in
           match uu____3446 with
           | (uu____3461,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3486 =
                 let uu____3491 =
                   let uu____3496 =
                     let uu____3497 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3497]  in
                   FStar_Syntax_Subst.open_term uu____3496 phi  in
                 match uu____3491 with
                 | (bvs,phi1) ->
                     let uu____3522 =
                       let uu____3523 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3523  in
                     (uu____3522, phi1)
                  in
               (match uu____3486 with
                | (bv1,phi1) ->
                    let uu____3542 =
                      let uu____3545 = FStar_Tactics_Types.goal_env g  in
                      let uu____3546 =
                        let uu____3547 =
                          let uu____3550 =
                            let uu____3551 =
                              let uu____3558 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3558)  in
                            FStar_Syntax_Syntax.NT uu____3551  in
                          [uu____3550]  in
                        FStar_Syntax_Subst.subst uu____3547 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3545
                        uu____3546 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3542
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3566  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3436
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3585 = cur_goal ()  in
      bind uu____3585
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3593 = FStar_Tactics_Types.goal_env goal  in
               let uu____3594 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3593 uu____3594
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3596 = __tc env t  in
           bind uu____3596
             (fun uu____3615  ->
                match uu____3615 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3630  ->
                         let uu____3631 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3632 =
                           let uu____3633 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3633
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3631 uu____3632)
                      (fun uu____3636  ->
                         let uu____3637 =
                           let uu____3640 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3640 guard  in
                         bind uu____3637
                           (fun uu____3642  ->
                              mlog
                                (fun uu____3646  ->
                                   let uu____3647 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3648 =
                                     let uu____3649 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3649
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3647 uu____3648)
                                (fun uu____3652  ->
                                   let uu____3653 =
                                     let uu____3656 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3657 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3656 typ uu____3657  in
                                   bind uu____3653
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3663 =
                                             let uu____3664 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3664 t1  in
                                           let uu____3665 =
                                             let uu____3666 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3666 typ  in
                                           let uu____3667 =
                                             let uu____3668 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3669 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3668 uu____3669  in
                                           let uu____3670 =
                                             let uu____3671 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3672 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3671 uu____3672  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3663 uu____3665 uu____3667
                                             uu____3670)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3687 =
        mlog
          (fun uu____3692  ->
             let uu____3693 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3693)
          (fun uu____3696  ->
             let uu____3697 =
               let uu____3704 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3704  in
             bind uu____3697
               (fun uu___343_3713  ->
                  match uu___343_3713 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3723  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3726  ->
                           let uu____3727 =
                             let uu____3734 =
                               let uu____3737 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3737
                                 (fun uu____3742  ->
                                    let uu____3743 = refine_intro ()  in
                                    bind uu____3743
                                      (fun uu____3747  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3734  in
                           bind uu____3727
                             (fun uu___342_3754  ->
                                match uu___342_3754 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3762 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3687
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3812 = f x  in
          bind uu____3812
            (fun y  ->
               let uu____3820 = mapM f xs  in
               bind uu____3820 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3891 = do_unify e ty1 ty2  in
          bind uu____3891
            (fun uu___344_3903  ->
               if uu___344_3903
               then ret acc
               else
                 (let uu____3922 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3922 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3943 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3944 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3943
                        uu____3944
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3959 =
                        let uu____3960 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3960  in
                      if uu____3959
                      then fail "Codomain is effectful"
                      else
                        (let uu____3980 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3980
                           (fun uu____4006  ->
                              match uu____4006 with
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
      let uu____4092 =
        mlog
          (fun uu____4097  ->
             let uu____4098 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4098)
          (fun uu____4101  ->
             let uu____4102 = cur_goal ()  in
             bind uu____4102
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4110 = __tc e tm  in
                  bind uu____4110
                    (fun uu____4131  ->
                       match uu____4131 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4144 =
                             let uu____4155 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4155  in
                           bind uu____4144
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4198  ->
                                       fun w  ->
                                         match uu____4198 with
                                         | (uvt,q,uu____4216) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4248 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4265  ->
                                       fun s  ->
                                         match uu____4265 with
                                         | (uu____4277,uu____4278,uv) ->
                                             let uu____4280 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4280) uvs uu____4248
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4289 = solve' goal w  in
                                bind uu____4289
                                  (fun uu____4294  ->
                                     let uu____4295 =
                                       mapM
                                         (fun uu____4312  ->
                                            match uu____4312 with
                                            | (uvt,q,uv) ->
                                                let uu____4324 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4324 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4329 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4330 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4330
                                                     then ret ()
                                                     else
                                                       (let uu____4334 =
                                                          let uu____4337 =
                                                            bnorm_goal
                                                              (let uu___382_4340
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___382_4340.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___382_4340.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4337]  in
                                                        add_goals uu____4334)))
                                         uvs
                                        in
                                     bind uu____4295
                                       (fun uu____4344  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4092
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4369 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4369
    then
      let uu____4376 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4391 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4444 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4376 with
      | (pre,post) ->
          let post1 =
            let uu____4476 =
              let uu____4487 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4487]  in
            FStar_Syntax_Util.mk_app post uu____4476  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4517 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4517
       then
         let uu____4524 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4524
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4557 =
      let uu____4560 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4567  ->
                  let uu____4568 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4568)
               (fun uu____4572  ->
                  let is_unit_t t =
                    let uu____4579 =
                      let uu____4580 = FStar_Syntax_Subst.compress t  in
                      uu____4580.FStar_Syntax_Syntax.n  in
                    match uu____4579 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4584 -> false  in
                  let uu____4585 = cur_goal ()  in
                  bind uu____4585
                    (fun goal  ->
                       let uu____4591 =
                         let uu____4600 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4600 tm  in
                       bind uu____4591
                         (fun uu____4615  ->
                            match uu____4615 with
                            | (tm1,t,guard) ->
                                let uu____4627 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4627 with
                                 | (bs,comp) ->
                                     let uu____4660 = lemma_or_sq comp  in
                                     (match uu____4660 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4679 =
                                            FStar_List.fold_left
                                              (fun uu____4727  ->
                                                 fun uu____4728  ->
                                                   match (uu____4727,
                                                           uu____4728)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4841 =
                                                         is_unit_t b_t  in
                                                       if uu____4841
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4879 =
                                                            let uu____4892 =
                                                              let uu____4893
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____4893.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____4896 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____4892
                                                              uu____4896 b_t
                                                             in
                                                          match uu____4879
                                                          with
                                                          | (u,uu____4914,g_u)
                                                              ->
                                                              let uu____4928
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4928,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4679 with
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
                                               let uu____5007 =
                                                 let uu____5010 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5011 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5012 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5010
                                                   uu____5011 uu____5012
                                                  in
                                               bind uu____5007
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5020 =
                                                        let uu____5021 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5021 tm1
                                                         in
                                                      let uu____5022 =
                                                        let uu____5023 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5024 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5023
                                                          uu____5024
                                                         in
                                                      let uu____5025 =
                                                        let uu____5026 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5027 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5026
                                                          uu____5027
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5020 uu____5022
                                                        uu____5025
                                                    else
                                                      (let uu____5029 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5029
                                                         (fun uu____5034  ->
                                                            let uu____5035 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5035
                                                              (fun uu____5043
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5068
                                                                    =
                                                                    let uu____5071
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5071
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5068
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
                                                                    let uu____5106
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5106)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5122
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5122
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5140)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5166)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5183
                                                                    -> false)
                                                                    in
                                                                 let uu____5184
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
                                                                    let uu____5214
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5214
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5236)
                                                                    ->
                                                                    let uu____5261
                                                                    =
                                                                    let uu____5262
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5262.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5261
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5270)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___383_5290
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___383_5290.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___383_5290.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___383_5290.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5293
                                                                    ->
                                                                    let env =
                                                                    let uu___384_5295
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___384_5295.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5297
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5297
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
                                                                    let uu____5300
                                                                    =
                                                                    let uu____5307
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5307
                                                                    term1  in
                                                                    match uu____5300
                                                                    with
                                                                    | 
                                                                    (uu____5308,uu____5309,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5311
                                                                    =
                                                                    let uu____5314
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5315
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5316
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5315
                                                                    uu____5316
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5318
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5314
                                                                    uu____5318
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5311
                                                                    (fun
                                                                    uu____5322
                                                                     ->
                                                                    ret []))))
                                                                    in
                                                                 bind
                                                                   uu____5184
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
                                                                    let uu____5384
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5384
                                                                    then
                                                                    let uu____5387
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5387
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
                                                                    let uu____5401
                                                                    =
                                                                    let uu____5402
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5402
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5401)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5403
                                                                    =
                                                                    let uu____5406
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5406
                                                                    guard  in
                                                                    bind
                                                                    uu____5403
                                                                    (fun
                                                                    uu____5409
                                                                     ->
                                                                    let uu____5410
                                                                    =
                                                                    let uu____5413
                                                                    =
                                                                    let uu____5414
                                                                    =
                                                                    let uu____5415
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5416
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5415
                                                                    uu____5416
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5414
                                                                     in
                                                                    if
                                                                    uu____5413
                                                                    then
                                                                    let uu____5419
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5419
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5410
                                                                    (fun
                                                                    uu____5422
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4560  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4557
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5444 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5444 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5454::(e1,uu____5456)::(e2,uu____5458)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5519 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5543 = destruct_eq' typ  in
    match uu____5543 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5573 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5573 with
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
        let uu____5635 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5635 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5683 = aux e'  in
               FStar_Util.map_opt uu____5683
                 (fun uu____5707  ->
                    match uu____5707 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5728 = aux e  in
      FStar_Util.map_opt uu____5728
        (fun uu____5752  ->
           match uu____5752 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5819 =
            let uu____5828 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5828  in
          FStar_Util.map_opt uu____5819
            (fun uu____5843  ->
               match uu____5843 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___385_5862 = bv  in
                     let uu____5863 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___385_5862.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___385_5862.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5863
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___386_5871 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5872 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5881 =
                       let uu____5884 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5884  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___386_5871.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5872;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5881;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___386_5871.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___386_5871.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___386_5871.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___387_5885 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___387_5885.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___387_5885.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___387_5885.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5895 =
      let uu____5898 = cur_goal ()  in
      bind uu____5898
        (fun goal  ->
           let uu____5906 = h  in
           match uu____5906 with
           | (bv,uu____5910) ->
               mlog
                 (fun uu____5918  ->
                    let uu____5919 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5920 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5919
                      uu____5920)
                 (fun uu____5923  ->
                    let uu____5924 =
                      let uu____5933 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5933  in
                    match uu____5924 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5954 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5954 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5969 =
                               let uu____5970 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5970.FStar_Syntax_Syntax.n  in
                             (match uu____5969 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___388_5987 = bv1  in
                                    let uu____5988 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___388_5987.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___388_5987.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5988
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___389_5996 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5997 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6006 =
                                      let uu____6009 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6009
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___389_5996.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5997;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6006;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___389_5996.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___389_5996.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___389_5996.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___390_6012 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___390_6012.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___390_6012.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___390_6012.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6013 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6014 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5895
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6039 =
        let uu____6042 = cur_goal ()  in
        bind uu____6042
          (fun goal  ->
             let uu____6053 = b  in
             match uu____6053 with
             | (bv,uu____6057) ->
                 let bv' =
                   let uu____6063 =
                     let uu___391_6064 = bv  in
                     let uu____6065 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6065;
                       FStar_Syntax_Syntax.index =
                         (uu___391_6064.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___391_6064.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6063  in
                 let s1 =
                   let uu____6069 =
                     let uu____6070 =
                       let uu____6077 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6077)  in
                     FStar_Syntax_Syntax.NT uu____6070  in
                   [uu____6069]  in
                 let uu____6082 = subst_goal bv bv' s1 goal  in
                 (match uu____6082 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6039
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6101 =
      let uu____6104 = cur_goal ()  in
      bind uu____6104
        (fun goal  ->
           let uu____6113 = b  in
           match uu____6113 with
           | (bv,uu____6117) ->
               let uu____6122 =
                 let uu____6131 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6131  in
               (match uu____6122 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6152 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6152 with
                     | (ty,u) ->
                         let uu____6161 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6161
                           (fun uu____6179  ->
                              match uu____6179 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___392_6189 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___392_6189.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___392_6189.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6193 =
                                      let uu____6194 =
                                        let uu____6201 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6201)  in
                                      FStar_Syntax_Syntax.NT uu____6194  in
                                    [uu____6193]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___393_6213 = b1  in
                                         let uu____6214 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___393_6213.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___393_6213.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6214
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6221  ->
                                       let new_goal =
                                         let uu____6223 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6224 =
                                           let uu____6225 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6225
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6223 uu____6224
                                          in
                                       let uu____6226 = add_goals [new_goal]
                                          in
                                       bind uu____6226
                                         (fun uu____6231  ->
                                            let uu____6232 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6232
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6101
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6255 =
        let uu____6258 = cur_goal ()  in
        bind uu____6258
          (fun goal  ->
             let uu____6267 = b  in
             match uu____6267 with
             | (bv,uu____6271) ->
                 let uu____6276 =
                   let uu____6285 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6285  in
                 (match uu____6276 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6309 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6309
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___394_6314 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___394_6314.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___394_6314.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6316 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6316))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6255
  
let (revert : unit -> unit tac) =
  fun uu____6327  ->
    let uu____6330 = cur_goal ()  in
    bind uu____6330
      (fun goal  ->
         let uu____6336 =
           let uu____6343 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6343  in
         match uu____6336 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6359 =
                 let uu____6362 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6362  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6359
                in
             let uu____6377 = new_uvar "revert" env' typ'  in
             bind uu____6377
               (fun uu____6392  ->
                  match uu____6392 with
                  | (r,u_r) ->
                      let uu____6401 =
                        let uu____6404 =
                          let uu____6405 =
                            let uu____6406 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6406.FStar_Syntax_Syntax.pos  in
                          let uu____6409 =
                            let uu____6414 =
                              let uu____6415 =
                                let uu____6424 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6424  in
                              [uu____6415]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6414  in
                          uu____6409 FStar_Pervasives_Native.None uu____6405
                           in
                        set_solution goal uu____6404  in
                      bind uu____6401
                        (fun uu____6445  ->
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
      let uu____6457 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6457
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6472 = cur_goal ()  in
    bind uu____6472
      (fun goal  ->
         mlog
           (fun uu____6480  ->
              let uu____6481 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6482 =
                let uu____6483 =
                  let uu____6484 =
                    let uu____6493 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6493  in
                  FStar_All.pipe_right uu____6484 FStar_List.length  in
                FStar_All.pipe_right uu____6483 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6481 uu____6482)
           (fun uu____6510  ->
              let uu____6511 =
                let uu____6520 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6520  in
              match uu____6511 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6559 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6559
                        then
                          let uu____6562 =
                            let uu____6563 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6563
                             in
                          fail uu____6562
                        else check1 bvs2
                     in
                  let uu____6565 =
                    let uu____6566 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6566  in
                  if uu____6565
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6570 = check1 bvs  in
                     bind uu____6570
                       (fun uu____6576  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6578 =
                            let uu____6585 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6585  in
                          bind uu____6578
                            (fun uu____6594  ->
                               match uu____6594 with
                               | (ut,uvar_ut) ->
                                   let uu____6603 = set_solution goal ut  in
                                   bind uu____6603
                                     (fun uu____6608  ->
                                        let uu____6609 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6609))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6616  ->
    let uu____6619 = cur_goal ()  in
    bind uu____6619
      (fun goal  ->
         let uu____6625 =
           let uu____6632 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6632  in
         match uu____6625 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6640) ->
             let uu____6645 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6645)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6655 = cur_goal ()  in
    bind uu____6655
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6665 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6665  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6668  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6678 = cur_goal ()  in
    bind uu____6678
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6688 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6688  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6691  -> add_goals [g']))
  
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
            let uu____6731 = FStar_Syntax_Subst.compress t  in
            uu____6731.FStar_Syntax_Syntax.n  in
          let uu____6734 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___398_6740 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___398_6740.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___398_6740.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6734
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6756 =
                   let uu____6757 = FStar_Syntax_Subst.compress t1  in
                   uu____6757.FStar_Syntax_Syntax.n  in
                 match uu____6756 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6788 = ff hd1  in
                     bind uu____6788
                       (fun hd2  ->
                          let fa uu____6814 =
                            match uu____6814 with
                            | (a,q) ->
                                let uu____6835 = ff a  in
                                bind uu____6835 (fun a1  -> ret (a1, q))
                             in
                          let uu____6854 = mapM fa args  in
                          bind uu____6854
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6936 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6936 with
                      | (bs1,t') ->
                          let uu____6945 =
                            let uu____6948 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6948 t'  in
                          bind uu____6945
                            (fun t''  ->
                               let uu____6952 =
                                 let uu____6953 =
                                   let uu____6972 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6981 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6972, uu____6981, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6953  in
                               ret uu____6952))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7056 = ff hd1  in
                     bind uu____7056
                       (fun hd2  ->
                          let ffb br =
                            let uu____7071 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7071 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7103 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7103  in
                                let uu____7104 = ff1 e  in
                                bind uu____7104
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7119 = mapM ffb brs  in
                          bind uu____7119
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7163;
                          FStar_Syntax_Syntax.lbtyp = uu____7164;
                          FStar_Syntax_Syntax.lbeff = uu____7165;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7167;
                          FStar_Syntax_Syntax.lbpos = uu____7168;_}::[]),e)
                     ->
                     let lb =
                       let uu____7193 =
                         let uu____7194 = FStar_Syntax_Subst.compress t1  in
                         uu____7194.FStar_Syntax_Syntax.n  in
                       match uu____7193 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7198) -> lb
                       | uu____7211 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7220 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7220
                         (fun def1  ->
                            ret
                              (let uu___395_7226 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___395_7226.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___395_7226.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___395_7226.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___395_7226.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___395_7226.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___395_7226.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7227 = fflb lb  in
                     bind uu____7227
                       (fun lb1  ->
                          let uu____7237 =
                            let uu____7242 =
                              let uu____7243 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7243]  in
                            FStar_Syntax_Subst.open_term uu____7242 e  in
                          match uu____7237 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7273 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7273  in
                              let uu____7274 = ff1 e1  in
                              bind uu____7274
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7315 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7315
                         (fun def  ->
                            ret
                              (let uu___396_7321 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___396_7321.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___396_7321.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___396_7321.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___396_7321.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___396_7321.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___396_7321.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7322 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7322 with
                      | (lbs1,e1) ->
                          let uu____7337 = mapM fflb lbs1  in
                          bind uu____7337
                            (fun lbs2  ->
                               let uu____7349 = ff e1  in
                               bind uu____7349
                                 (fun e2  ->
                                    let uu____7357 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7357 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7425 = ff t2  in
                     bind uu____7425
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7456 = ff t2  in
                     bind uu____7456
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7463 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___397_7470 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___397_7470.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___397_7470.FStar_Syntax_Syntax.vars)
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
            let uu____7507 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___399_7516 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___399_7516.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___399_7516.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___399_7516.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___399_7516.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___399_7516.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___399_7516.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___399_7516.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___399_7516.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___399_7516.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___399_7516.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___399_7516.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___399_7516.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___399_7516.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___399_7516.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___399_7516.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___399_7516.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___399_7516.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___399_7516.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___399_7516.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___399_7516.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___399_7516.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___399_7516.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___399_7516.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___399_7516.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___399_7516.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___399_7516.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___399_7516.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___399_7516.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___399_7516.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___399_7516.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___399_7516.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___399_7516.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___399_7516.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___399_7516.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___399_7516.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___399_7516.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___399_7516.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___399_7516.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___399_7516.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___399_7516.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___399_7516.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7507 with
            | (t1,lcomp,g) ->
                let uu____7522 =
                  (let uu____7525 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7525) ||
                    (let uu____7527 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7527)
                   in
                if uu____7522
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7535 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7535
                       (fun uu____7551  ->
                          match uu____7551 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7564  ->
                                    let uu____7565 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7566 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7565 uu____7566);
                               (let uu____7567 =
                                  let uu____7570 =
                                    let uu____7571 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7571 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7570
                                    opts
                                   in
                                bind uu____7567
                                  (fun uu____7574  ->
                                     let uu____7575 =
                                       bind tau
                                         (fun uu____7581  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7587  ->
                                                 let uu____7588 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7589 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7588 uu____7589);
                                            ret ut1)
                                        in
                                     focus uu____7575))))
                      in
                   let uu____7590 = trytac' rewrite_eq  in
                   bind uu____7590
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
          let uu____7788 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7788
            (fun t1  ->
               let uu____7796 =
                 f env
                   (let uu___402_7805 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___402_7805.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___402_7805.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7796
                 (fun uu____7821  ->
                    match uu____7821 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7844 =
                               let uu____7845 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7845.FStar_Syntax_Syntax.n  in
                             match uu____7844 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7882 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7882
                                   (fun uu____7907  ->
                                      match uu____7907 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7923 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7923
                                            (fun uu____7950  ->
                                               match uu____7950 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___400_7980 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___400_7980.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___400_7980.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8022 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8022 with
                                  | (bs1,t') ->
                                      let uu____8037 =
                                        let uu____8044 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8044 ctrl1 t'
                                         in
                                      bind uu____8037
                                        (fun uu____8062  ->
                                           match uu____8062 with
                                           | (t'',ctrl2) ->
                                               let uu____8077 =
                                                 let uu____8084 =
                                                   let uu___401_8087 = t4  in
                                                   let uu____8090 =
                                                     let uu____8091 =
                                                       let uu____8110 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8119 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8110,
                                                         uu____8119, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8091
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8090;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___401_8087.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___401_8087.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8084, ctrl2)  in
                                               ret uu____8077))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8172 -> ret (t3, ctrl1))))

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
              let uu____8219 = ctrl_tac_fold f env ctrl t  in
              bind uu____8219
                (fun uu____8243  ->
                   match uu____8243 with
                   | (t1,ctrl1) ->
                       let uu____8258 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8258
                         (fun uu____8285  ->
                            match uu____8285 with
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
              let uu____8369 =
                let uu____8376 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8376
                  (fun uu____8385  ->
                     let uu____8386 = ctrl t1  in
                     bind uu____8386
                       (fun res  ->
                          let uu____8409 = trivial ()  in
                          bind uu____8409 (fun uu____8417  -> ret res)))
                 in
              bind uu____8369
                (fun uu____8433  ->
                   match uu____8433 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8457 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___403_8466 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___403_8466.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___403_8466.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___403_8466.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___403_8466.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___403_8466.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___403_8466.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___403_8466.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___403_8466.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___403_8466.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___403_8466.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___403_8466.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___403_8466.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___403_8466.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___403_8466.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___403_8466.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___403_8466.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___403_8466.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___403_8466.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___403_8466.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___403_8466.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___403_8466.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___403_8466.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___403_8466.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___403_8466.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___403_8466.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___403_8466.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___403_8466.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___403_8466.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___403_8466.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___403_8466.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___403_8466.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___403_8466.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___403_8466.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___403_8466.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___403_8466.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___403_8466.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___403_8466.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___403_8466.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___403_8466.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___403_8466.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___403_8466.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8457 with
                          | (t2,lcomp,g) ->
                              let uu____8476 =
                                (let uu____8479 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8479) ||
                                  (let uu____8481 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8481)
                                 in
                              if uu____8476
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8494 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8494
                                   (fun uu____8514  ->
                                      match uu____8514 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8531  ->
                                                let uu____8532 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8533 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8532 uu____8533);
                                           (let uu____8534 =
                                              let uu____8537 =
                                                let uu____8538 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8538 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8537 opts
                                               in
                                            bind uu____8534
                                              (fun uu____8545  ->
                                                 let uu____8546 =
                                                   bind rewriter
                                                     (fun uu____8560  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8566  ->
                                                             let uu____8567 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8568 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8567
                                                               uu____8568);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8546)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8609 =
        bind get
          (fun ps  ->
             let uu____8619 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8619 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8656  ->
                       let uu____8657 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8657);
                  bind dismiss_all
                    (fun uu____8660  ->
                       let uu____8661 =
                         let uu____8668 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8668
                           keepGoing gt1
                          in
                       bind uu____8661
                         (fun uu____8680  ->
                            match uu____8680 with
                            | (gt',uu____8688) ->
                                (log ps
                                   (fun uu____8692  ->
                                      let uu____8693 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8693);
                                 (let uu____8694 = push_goals gs  in
                                  bind uu____8694
                                    (fun uu____8699  ->
                                       let uu____8700 =
                                         let uu____8703 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8703]  in
                                       add_goals uu____8700)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8609
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8726 =
        bind get
          (fun ps  ->
             let uu____8736 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8736 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8773  ->
                       let uu____8774 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8774);
                  bind dismiss_all
                    (fun uu____8777  ->
                       let uu____8778 =
                         let uu____8781 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8781 gt1
                          in
                       bind uu____8778
                         (fun gt'  ->
                            log ps
                              (fun uu____8789  ->
                                 let uu____8790 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8790);
                            (let uu____8791 = push_goals gs  in
                             bind uu____8791
                               (fun uu____8796  ->
                                  let uu____8797 =
                                    let uu____8800 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8800]  in
                                  add_goals uu____8797))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8726
  
let (trefl : unit -> unit tac) =
  fun uu____8811  ->
    let uu____8814 =
      let uu____8817 = cur_goal ()  in
      bind uu____8817
        (fun g  ->
           let uu____8835 =
             let uu____8840 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8840  in
           match uu____8835 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8848 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8848 with
                | (hd1,args) ->
                    let uu____8887 =
                      let uu____8900 =
                        let uu____8901 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8901.FStar_Syntax_Syntax.n  in
                      (uu____8900, args)  in
                    (match uu____8887 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8915::(l,uu____8917)::(r,uu____8919)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8966 =
                           let uu____8969 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8969 l r  in
                         bind uu____8966
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____8976 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8976 l
                                    in
                                 let r1 =
                                   let uu____8978 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____8978 r
                                    in
                                 let uu____8979 =
                                   let uu____8982 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____8982 l1 r1  in
                                 bind uu____8979
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____8988 =
                                           let uu____8989 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8989 l1  in
                                         let uu____8990 =
                                           let uu____8991 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____8991 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____8988 uu____8990))))
                     | (hd2,uu____8993) ->
                         let uu____9010 =
                           let uu____9011 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9011 t  in
                         fail1 "trefl: not an equality (%s)" uu____9010))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8814
  
let (dup : unit -> unit tac) =
  fun uu____9024  ->
    let uu____9027 = cur_goal ()  in
    bind uu____9027
      (fun g  ->
         let uu____9033 =
           let uu____9040 = FStar_Tactics_Types.goal_env g  in
           let uu____9041 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9040 uu____9041  in
         bind uu____9033
           (fun uu____9050  ->
              match uu____9050 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___404_9060 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___404_9060.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___404_9060.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___404_9060.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9063  ->
                       let uu____9064 =
                         let uu____9067 = FStar_Tactics_Types.goal_env g  in
                         let uu____9068 =
                           let uu____9069 =
                             let uu____9070 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9071 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9070
                               uu____9071
                              in
                           let uu____9072 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9073 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9069 uu____9072 u
                             uu____9073
                            in
                         add_irrelevant_goal "dup equation" uu____9067
                           uu____9068 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9064
                         (fun uu____9076  ->
                            let uu____9077 = add_goals [g']  in
                            bind uu____9077 (fun uu____9081  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9088  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___405_9105 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___405_9105.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___405_9105.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___405_9105.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___405_9105.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___405_9105.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___405_9105.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___405_9105.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___405_9105.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___405_9105.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___405_9105.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___405_9105.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9106 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9115  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___406_9128 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___406_9128.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___406_9128.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___406_9128.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___406_9128.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___406_9128.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___406_9128.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___406_9128.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___406_9128.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___406_9128.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___406_9128.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___406_9128.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9135  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9142 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9162 =
      let uu____9169 = cur_goal ()  in
      bind uu____9169
        (fun g  ->
           let uu____9179 =
             let uu____9188 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9188 t  in
           bind uu____9179
             (fun uu____9216  ->
                match uu____9216 with
                | (t1,typ,guard) ->
                    let uu____9232 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9232 with
                     | (hd1,args) ->
                         let uu____9281 =
                           let uu____9296 =
                             let uu____9297 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9297.FStar_Syntax_Syntax.n  in
                           (uu____9296, args)  in
                         (match uu____9281 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9318)::(q,uu____9320)::[]) when
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
                                let uu____9374 =
                                  let uu____9375 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9375
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9374
                                 in
                              let g2 =
                                let uu____9377 =
                                  let uu____9378 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9378
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9377
                                 in
                              bind __dismiss
                                (fun uu____9385  ->
                                   let uu____9386 = add_goals [g1; g2]  in
                                   bind uu____9386
                                     (fun uu____9395  ->
                                        let uu____9396 =
                                          let uu____9401 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9402 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9401, uu____9402)  in
                                        ret uu____9396))
                          | uu____9407 ->
                              let uu____9422 =
                                let uu____9423 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9423 typ  in
                              fail1 "Not a disjunction: %s" uu____9422))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9162
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9453 =
      let uu____9456 = cur_goal ()  in
      bind uu____9456
        (fun g  ->
           FStar_Options.push ();
           (let uu____9469 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9469);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___407_9476 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___407_9476.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___407_9476.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___407_9476.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9453
  
let (top_env : unit -> env tac) =
  fun uu____9488  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9501  ->
    let uu____9504 = cur_goal ()  in
    bind uu____9504
      (fun g  ->
         let uu____9510 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9510)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9519  ->
    let uu____9522 = cur_goal ()  in
    bind uu____9522
      (fun g  ->
         let uu____9528 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9528)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9537  ->
    let uu____9540 = cur_goal ()  in
    bind uu____9540
      (fun g  ->
         let uu____9546 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9546)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9555  ->
    let uu____9558 = cur_env ()  in
    bind uu____9558
      (fun e  ->
         let uu____9564 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____9564)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9579 =
        mlog
          (fun uu____9584  ->
             let uu____9585 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9585)
          (fun uu____9588  ->
             let uu____9589 = cur_goal ()  in
             bind uu____9589
               (fun goal  ->
                  let env =
                    let uu____9597 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9597 ty  in
                  let uu____9598 = __tc env tm  in
                  bind uu____9598
                    (fun uu____9617  ->
                       match uu____9617 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9631  ->
                                let uu____9632 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9632)
                             (fun uu____9634  ->
                                mlog
                                  (fun uu____9637  ->
                                     let uu____9638 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9638)
                                  (fun uu____9641  ->
                                     let uu____9642 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9642
                                       (fun uu____9646  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9579
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9669 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9675 =
              let uu____9682 =
                let uu____9683 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9683
                 in
              new_uvar "uvar_env.2" env uu____9682  in
            bind uu____9675
              (fun uu____9699  ->
                 match uu____9699 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9669
        (fun typ  ->
           let uu____9711 = new_uvar "uvar_env" env typ  in
           bind uu____9711
             (fun uu____9725  -> match uu____9725 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9743 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9762 -> g.FStar_Tactics_Types.opts
             | uu____9765 -> FStar_Options.peek ()  in
           let uu____9768 = FStar_Syntax_Util.head_and_args t  in
           match uu____9768 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9788);
                FStar_Syntax_Syntax.pos = uu____9789;
                FStar_Syntax_Syntax.vars = uu____9790;_},uu____9791)
               ->
               let env1 =
                 let uu___408_9833 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___408_9833.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___408_9833.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___408_9833.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___408_9833.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___408_9833.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___408_9833.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___408_9833.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___408_9833.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___408_9833.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___408_9833.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___408_9833.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___408_9833.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___408_9833.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___408_9833.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___408_9833.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___408_9833.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___408_9833.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___408_9833.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___408_9833.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___408_9833.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___408_9833.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___408_9833.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___408_9833.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___408_9833.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___408_9833.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___408_9833.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___408_9833.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___408_9833.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___408_9833.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___408_9833.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___408_9833.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___408_9833.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___408_9833.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___408_9833.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___408_9833.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___408_9833.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___408_9833.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___408_9833.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___408_9833.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___408_9833.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___408_9833.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9835 =
                 let uu____9838 = bnorm_goal g  in [uu____9838]  in
               add_goals uu____9835
           | uu____9839 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9743
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9888 = if b then t2 else ret false  in
             bind uu____9888 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9899 = trytac comp  in
      bind uu____9899
        (fun uu___345_9907  ->
           match uu___345_9907 with
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
        let uu____9933 =
          bind get
            (fun ps  ->
               let uu____9939 = __tc e t1  in
               bind uu____9939
                 (fun uu____9959  ->
                    match uu____9959 with
                    | (t11,ty1,g1) ->
                        let uu____9971 = __tc e t2  in
                        bind uu____9971
                          (fun uu____9991  ->
                             match uu____9991 with
                             | (t21,ty2,g2) ->
                                 let uu____10003 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10003
                                   (fun uu____10008  ->
                                      let uu____10009 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10009
                                        (fun uu____10015  ->
                                           let uu____10016 =
                                             do_unify e ty1 ty2  in
                                           let uu____10019 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10016 uu____10019)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9933
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10052  ->
             let uu____10053 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10053
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
        (fun uu____10074  ->
           let uu____10075 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10075)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10085 =
      mlog
        (fun uu____10090  ->
           let uu____10091 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10091)
        (fun uu____10094  ->
           let uu____10095 = cur_goal ()  in
           bind uu____10095
             (fun g  ->
                let uu____10101 =
                  let uu____10110 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10110 ty  in
                bind uu____10101
                  (fun uu____10122  ->
                     match uu____10122 with
                     | (ty1,uu____10132,guard) ->
                         let uu____10134 =
                           let uu____10137 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10137 guard  in
                         bind uu____10134
                           (fun uu____10140  ->
                              let uu____10141 =
                                let uu____10144 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10145 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10144 uu____10145 ty1  in
                              bind uu____10141
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10151 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10151
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
                                        let uu____10157 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10158 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10157
                                          uu____10158
                                         in
                                      let nty =
                                        let uu____10160 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10160 ty1  in
                                      let uu____10161 =
                                        let uu____10164 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10164 ng nty  in
                                      bind uu____10161
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10170 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10170
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10085
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10233 =
      let uu____10242 = cur_goal ()  in
      bind uu____10242
        (fun g  ->
           let uu____10254 =
             let uu____10263 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10263 s_tm  in
           bind uu____10254
             (fun uu____10281  ->
                match uu____10281 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10299 =
                      let uu____10302 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10302 guard  in
                    bind uu____10299
                      (fun uu____10314  ->
                         let uu____10315 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10315 with
                         | (h,args) ->
                             let uu____10360 =
                               let uu____10367 =
                                 let uu____10368 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10368.FStar_Syntax_Syntax.n  in
                               match uu____10367 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10383;
                                      FStar_Syntax_Syntax.vars = uu____10384;_},us)
                                   -> ret (fv, us)
                               | uu____10394 -> fail "type is not an fv"  in
                             bind uu____10360
                               (fun uu____10414  ->
                                  match uu____10414 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10430 =
                                        let uu____10433 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10433 t_lid
                                         in
                                      (match uu____10430 with
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
                                                  (fun uu____10482  ->
                                                     let uu____10483 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10483 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10498 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10526
                                                                  =
                                                                  let uu____10529
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10529
                                                                    c_lid
                                                                   in
                                                                match uu____10526
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
                                                                    uu____10599
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
                                                                    let uu____10604
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10604
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10627
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10627
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10670
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10670
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____10743
                                                                    =
                                                                    let uu____10744
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____10744
                                                                     in
                                                                    failwhen
                                                                    uu____10743
                                                                    "not total?"
                                                                    (fun
                                                                    uu____10761
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
                                                                    uu___346_10777
                                                                    =
                                                                    match uu___346_10777
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____10780)
                                                                    -> true
                                                                    | 
                                                                    uu____10781
                                                                    -> false
                                                                     in
                                                                    let uu____10784
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____10784
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
                                                                    uu____10917
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
                                                                    uu____10979
                                                                     ->
                                                                    match uu____10979
                                                                    with
                                                                    | 
                                                                    ((bv,uu____10999),
                                                                    (t,uu____11001))
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
                                                                    uu____11069
                                                                     ->
                                                                    match uu____11069
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11095),
                                                                    (t,uu____11097))
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
                                                                    uu____11152
                                                                     ->
                                                                    match uu____11152
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
                                                                    let uu____11202
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___409_11219
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___409_11219.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11202
                                                                    with
                                                                    | 
                                                                    (uu____11232,uu____11233,uu____11234,pat_t,uu____11236,uu____11237)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11243
                                                                    =
                                                                    let uu____11244
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11244
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11243
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11248
                                                                    =
                                                                    let uu____11257
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11257]
                                                                     in
                                                                    let uu____11276
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11248
                                                                    uu____11276
                                                                     in
                                                                    let nty =
                                                                    let uu____11282
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11282
                                                                     in
                                                                    let uu____11285
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11285
                                                                    (fun
                                                                    uu____11314
                                                                     ->
                                                                    match uu____11314
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
                                                                    let uu____11340
                                                                    =
                                                                    let uu____11351
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11351]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11340
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11387
                                                                    =
                                                                    let uu____11398
                                                                    =
                                                                    let uu____11403
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11403)
                                                                     in
                                                                    (g', br,
                                                                    uu____11398)
                                                                     in
                                                                    ret
                                                                    uu____11387))))))
                                                                    | 
                                                                    uu____11424
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10498
                                                           (fun goal_brs  ->
                                                              let uu____11473
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11473
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
                                                                  let uu____11546
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11546
                                                                    (
                                                                    fun
                                                                    uu____11557
                                                                     ->
                                                                    let uu____11558
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11558
                                                                    (fun
                                                                    uu____11568
                                                                     ->
                                                                    ret infos))))
                                            | uu____11575 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10233
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11620::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11648 = init xs  in x :: uu____11648
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11660 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____11668) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____11733 = last args  in
          (match uu____11733 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____11763 =
                 let uu____11764 =
                   let uu____11769 =
                     let uu____11770 =
                       let uu____11775 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____11775  in
                     uu____11770 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____11769, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____11764  in
               FStar_All.pipe_left ret uu____11763)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____11788,uu____11789) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____11841 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____11841 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____11882 =
                      let uu____11883 =
                        let uu____11888 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____11888)  in
                      FStar_Reflection_Data.Tv_Abs uu____11883  in
                    FStar_All.pipe_left ret uu____11882))
      | FStar_Syntax_Syntax.Tm_type uu____11891 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____11915 ->
          let uu____11930 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____11930 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____11960 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____11960 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12013 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12025 =
            let uu____12026 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12026  in
          FStar_All.pipe_left ret uu____12025
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12047 =
            let uu____12048 =
              let uu____12053 =
                let uu____12054 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12054  in
              (uu____12053, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12048  in
          FStar_All.pipe_left ret uu____12047
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12088 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12093 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12093 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12146 ->
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
             | FStar_Util.Inr uu____12180 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12184 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12184 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12204 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12208 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12262 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12262
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12281 =
                  let uu____12288 =
                    FStar_List.map
                      (fun uu____12300  ->
                         match uu____12300 with
                         | (p1,uu____12308) -> inspect_pat p1) ps
                     in
                  (fv, uu____12288)  in
                FStar_Reflection_Data.Pat_Cons uu____12281
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
              (fun uu___347_12402  ->
                 match uu___347_12402 with
                 | (pat,uu____12424,t4) ->
                     let uu____12442 = inspect_pat pat  in (uu____12442, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12451 ->
          ((let uu____12453 =
              let uu____12458 =
                let uu____12459 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____12460 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12459 uu____12460
                 in
              (FStar_Errors.Warning_CantInspect, uu____12458)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____12453);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11660
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12473 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12473
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12477 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12477
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12481 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12481
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12488 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12488
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12513 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12513
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12530 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12530
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12549 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12549
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12553 =
          let uu____12554 =
            let uu____12561 =
              let uu____12562 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12562  in
            FStar_Syntax_Syntax.mk uu____12561  in
          uu____12554 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12553
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12570 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12570
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12579 =
          let uu____12580 =
            let uu____12587 =
              let uu____12588 =
                let uu____12601 =
                  let uu____12604 =
                    let uu____12605 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12605]  in
                  FStar_Syntax_Subst.close uu____12604 t2  in
                ((false, [lb]), uu____12601)  in
              FStar_Syntax_Syntax.Tm_let uu____12588  in
            FStar_Syntax_Syntax.mk uu____12587  in
          uu____12580 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12579
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12645 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12645 with
         | (lbs,body) ->
             let uu____12660 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12660)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12694 =
                let uu____12695 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12695  in
              FStar_All.pipe_left wrap uu____12694
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12702 =
                let uu____12703 =
                  let uu____12716 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____12732 = pack_pat p1  in
                         (uu____12732, false)) ps
                     in
                  (fv, uu____12716)  in
                FStar_Syntax_Syntax.Pat_cons uu____12703  in
              FStar_All.pipe_left wrap uu____12702
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
            (fun uu___348_12778  ->
               match uu___348_12778 with
               | (pat,t1) ->
                   let uu____12795 = pack_pat pat  in
                   (uu____12795, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____12843 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12843
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____12871 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12871
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12917 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12917
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____12956 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12956
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____12977 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____12977 with
      | (u,ctx_uvars,g_u) ->
          let uu____13009 = FStar_List.hd ctx_uvars  in
          (match uu____13009 with
           | (ctx_uvar,uu____13023) ->
               let g =
                 let uu____13025 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13025 false
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
        let uu____13045 = goal_of_goal_ty env typ  in
        match uu____13045 with
        | (g,g_u) ->
            let ps =
              let uu____13057 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13057
              }  in
            let uu____13062 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13062)
  