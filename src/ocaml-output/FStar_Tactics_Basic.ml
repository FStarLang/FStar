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
      try (fun uu___355_154  -> match () with | () -> t.tac_f p) ()
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
  
let catch : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
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
                     (uu___356_1034.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (uu___356_1034.FStar_Tactics_Types.local_state)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1061 = catch t  in
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
           (fun uu___358_1119  ->
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
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___359_1220 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1220.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1220.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1220.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___359_1220.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1220.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1220.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1220.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1220.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1220.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1220.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1220.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___359_1220.FStar_Tactics_Types.local_state)
            }))
  
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1241 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1241
         then
           let uu____1242 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1243 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1242
             uu____1243
         else ());
        (try
           (fun uu___361_1250  ->
              match () with
              | () ->
                  let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
                  ((let uu____1257 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1257
                    then
                      let uu____1258 =
                        FStar_Common.string_of_option
                          (FStar_TypeChecker_Rel.guard_to_string env) res
                         in
                      let uu____1259 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____1260 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.print3
                        "%%%%%%%%do_unify (RESULT %s) %s =? %s\n" uu____1258
                        uu____1259 uu____1260
                    else ());
                   (match res with
                    | FStar_Pervasives_Native.None  -> ret false
                    | FStar_Pervasives_Native.Some g ->
                        let uu____1265 =
                          add_implicits g.FStar_TypeChecker_Env.implicits  in
                        bind uu____1265 (fun uu____1269  -> ret true)))) ()
         with
         | FStar_Errors.Err (uu____1276,msg) ->
             mlog
               (fun uu____1279  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1281  -> ret false)
         | FStar_Errors.Error (uu____1282,msg,r) ->
             mlog
               (fun uu____1287  ->
                  let uu____1288 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1288) (fun uu____1290  -> ret false))
  
let (compress_implicits : unit tac) =
  bind get
    (fun ps  ->
       let imps = ps.FStar_Tactics_Types.all_implicits  in
       let g =
         let uu___362_1301 = FStar_TypeChecker_Env.trivial_guard  in
         {
           FStar_TypeChecker_Env.guard_f =
             (uu___362_1301.FStar_TypeChecker_Env.guard_f);
           FStar_TypeChecker_Env.deferred =
             (uu___362_1301.FStar_TypeChecker_Env.deferred);
           FStar_TypeChecker_Env.univ_ineqs =
             (uu___362_1301.FStar_TypeChecker_Env.univ_ineqs);
           FStar_TypeChecker_Env.implicits = imps
         }  in
       let g1 =
         FStar_TypeChecker_Rel.resolve_implicits_tac
           ps.FStar_Tactics_Types.main_context g
          in
       let ps' =
         let uu___363_1304 = ps  in
         {
           FStar_Tactics_Types.main_context =
             (uu___363_1304.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___363_1304.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (g1.FStar_TypeChecker_Env.implicits);
           FStar_Tactics_Types.goals =
             (uu___363_1304.FStar_Tactics_Types.goals);
           FStar_Tactics_Types.smt_goals =
             (uu___363_1304.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___363_1304.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___363_1304.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___363_1304.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___363_1304.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___363_1304.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___363_1304.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___363_1304.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___363_1304.FStar_Tactics_Types.local_state)
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
          (fun uu____1327  ->
             (let uu____1329 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1329
              then
                (FStar_Options.push ();
                 (let uu____1331 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1333 = __do_unify env t1 t2  in
              bind uu____1333
                (fun r  ->
                   (let uu____1340 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1340 then FStar_Options.pop () else ());
                   bind compress_implicits (fun uu____1343  -> ret r))))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___364_1350 = ps  in
         let uu____1351 =
           FStar_List.filter
             (fun g  ->
                let uu____1357 = check_goal_solved g  in
                FStar_Option.isNone uu____1357) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___364_1350.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___364_1350.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___364_1350.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1351;
           FStar_Tactics_Types.smt_goals =
             (uu___364_1350.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___364_1350.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___364_1350.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___364_1350.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___364_1350.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___364_1350.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___364_1350.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___364_1350.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___364_1350.FStar_Tactics_Types.local_state)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1374 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1374 with
      | FStar_Pervasives_Native.Some uu____1379 ->
          let uu____1380 =
            let uu____1381 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1381  in
          fail uu____1380
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1397 = FStar_Tactics_Types.goal_env goal  in
      let uu____1398 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1397 solution uu____1398
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1404 =
         let uu___365_1405 = p  in
         let uu____1406 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___365_1405.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___365_1405.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___365_1405.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1406;
           FStar_Tactics_Types.smt_goals =
             (uu___365_1405.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___365_1405.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___365_1405.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___365_1405.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___365_1405.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___365_1405.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___365_1405.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___365_1405.FStar_Tactics_Types.tac_verb_dbg);
           FStar_Tactics_Types.local_state =
             (uu___365_1405.FStar_Tactics_Types.local_state)
         }  in
       set uu____1404)
  
let (dismiss : unit -> unit tac) =
  fun uu____1415  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1422 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1443  ->
           let uu____1444 =
             let uu____1445 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1445  in
           let uu____1446 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1444 uu____1446)
        (fun uu____1449  ->
           let uu____1450 = trysolve goal solution  in
           bind uu____1450
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1458  -> remove_solved_goals)
                else
                  (let uu____1460 =
                     let uu____1461 =
                       let uu____1462 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1462 solution  in
                     let uu____1463 =
                       let uu____1464 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1465 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1464 uu____1465  in
                     let uu____1466 =
                       let uu____1467 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1468 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1467 uu____1468  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1461 uu____1463 uu____1466
                      in
                   fail uu____1460)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1483 = set_solution goal solution  in
      bind uu____1483
        (fun uu____1487  ->
           bind __dismiss (fun uu____1489  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___366_1496 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___366_1496.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___366_1496.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___366_1496.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___366_1496.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___366_1496.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___366_1496.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___366_1496.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___366_1496.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___366_1496.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___366_1496.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___366_1496.FStar_Tactics_Types.tac_verb_dbg);
            FStar_Tactics_Types.local_state =
              (uu___366_1496.FStar_Tactics_Types.local_state)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1515 = FStar_Options.defensive ()  in
    if uu____1515
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1520 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1520)
         in
      let b2 =
        b1 &&
          (let uu____1523 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1523)
         in
      let rec aux b3 e =
        let uu____1535 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1535 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1553 =
        (let uu____1556 = aux b2 env  in Prims.op_Negation uu____1556) &&
          (let uu____1558 = FStar_ST.op_Bang nwarn  in
           uu____1558 < (Prims.parse_int "5"))
         in
      (if uu____1553
       then
         ((let uu____1579 =
             let uu____1580 = FStar_Tactics_Types.goal_type g  in
             uu____1580.FStar_Syntax_Syntax.pos  in
           let uu____1583 =
             let uu____1588 =
               let uu____1589 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1589
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1588)  in
           FStar_Errors.log_issue uu____1579 uu____1583);
          (let uu____1590 =
             let uu____1591 = FStar_ST.op_Bang nwarn  in
             uu____1591 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1590))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___367_1651 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___367_1651.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___367_1651.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___367_1651.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___367_1651.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___367_1651.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___367_1651.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___367_1651.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___367_1651.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___367_1651.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___367_1651.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___367_1651.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___367_1651.FStar_Tactics_Types.local_state)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___368_1671 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___368_1671.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___368_1671.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___368_1671.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___368_1671.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___368_1671.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___368_1671.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___368_1671.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___368_1671.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___368_1671.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___368_1671.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___368_1671.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___368_1671.FStar_Tactics_Types.local_state)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___369_1691 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___369_1691.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___369_1691.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___369_1691.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___369_1691.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___369_1691.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___369_1691.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___369_1691.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___369_1691.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___369_1691.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___369_1691.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___369_1691.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___369_1691.FStar_Tactics_Types.local_state)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___370_1711 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___370_1711.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___370_1711.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___370_1711.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___370_1711.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___370_1711.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___370_1711.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___370_1711.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___370_1711.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___370_1711.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___370_1711.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___370_1711.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___370_1711.FStar_Tactics_Types.local_state)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1722  -> add_goals [g]) 
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
        let uu____1750 =
          FStar_TypeChecker_Env.new_implicit_var_aux reason
            typ.FStar_Syntax_Syntax.pos env typ
            FStar_Syntax_Syntax.Allow_untyped
           in
        match uu____1750 with
        | (u,ctx_uvar,g_u) ->
            let uu____1784 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1784
              (fun uu____1793  ->
                 let uu____1794 =
                   let uu____1799 =
                     let uu____1800 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1800  in
                   (u, uu____1799)  in
                 ret uu____1794)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1818 = FStar_Syntax_Util.un_squash t  in
    match uu____1818 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1828 =
          let uu____1829 = FStar_Syntax_Subst.compress t'  in
          uu____1829.FStar_Syntax_Syntax.n  in
        (match uu____1828 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1833 -> false)
    | uu____1834 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1844 = FStar_Syntax_Util.un_squash t  in
    match uu____1844 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1854 =
          let uu____1855 = FStar_Syntax_Subst.compress t'  in
          uu____1855.FStar_Syntax_Syntax.n  in
        (match uu____1854 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1859 -> false)
    | uu____1860 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1871  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1882 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1882 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1889 = goal_to_string_verbose hd1  in
                    let uu____1890 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1889 uu____1890);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1897  ->
    let uu____1900 =
      bind get
        (fun ps  ->
           let uu____1906 = cur_goal ()  in
           bind uu____1906
             (fun g  ->
                (let uu____1913 =
                   let uu____1914 = FStar_Tactics_Types.goal_type g  in
                   uu____1914.FStar_Syntax_Syntax.pos  in
                 let uu____1917 =
                   let uu____1922 =
                     let uu____1923 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1923
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1922)  in
                 FStar_Errors.log_issue uu____1913 uu____1917);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1900
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1934  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___371_1944 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___371_1944.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___371_1944.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___371_1944.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___371_1944.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___371_1944.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___371_1944.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___371_1944.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___371_1944.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___371_1944.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___371_1944.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___371_1944.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (uu___371_1944.FStar_Tactics_Types.local_state)
           }  in
         let uu____1945 = set ps1  in
         bind uu____1945
           (fun uu____1950  ->
              let uu____1951 = FStar_BigInt.of_int_fs n1  in ret uu____1951))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1958  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1966 = FStar_BigInt.of_int_fs n1  in ret uu____1966)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1979  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1987 = FStar_BigInt.of_int_fs n1  in ret uu____1987)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____2000  ->
    let uu____2003 = cur_goal ()  in
    bind uu____2003 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2035 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2035 phi  in
          let uu____2036 = new_uvar reason env typ  in
          bind uu____2036
            (fun uu____2051  ->
               match uu____2051 with
               | (uu____2058,ctx_uvar) ->
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
             (fun uu____2103  ->
                let uu____2104 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2104)
             (fun uu____2107  ->
                let e1 =
                  let uu___372_2109 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___372_2109.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___372_2109.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___372_2109.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___372_2109.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___372_2109.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___372_2109.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___372_2109.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___372_2109.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___372_2109.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___372_2109.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___372_2109.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___372_2109.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___372_2109.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___372_2109.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___372_2109.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___372_2109.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___372_2109.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___372_2109.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___372_2109.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___372_2109.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___372_2109.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___372_2109.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___372_2109.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___372_2109.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___372_2109.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___372_2109.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___372_2109.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___372_2109.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___372_2109.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___372_2109.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___372_2109.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___372_2109.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___372_2109.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___372_2109.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___372_2109.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___372_2109.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___372_2109.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___372_2109.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___372_2109.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___372_2109.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___372_2109.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  (fun uu___374_2120  ->
                     match () with
                     | () ->
                         let uu____2129 =
                           (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                             e1 t
                            in
                         ret uu____2129) ()
                with
                | FStar_Errors.Err (uu____2156,msg) ->
                    let uu____2158 = tts e1 t  in
                    let uu____2159 =
                      let uu____2160 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2160
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2158 uu____2159 msg
                | FStar_Errors.Error (uu____2167,msg,uu____2169) ->
                    let uu____2170 = tts e1 t  in
                    let uu____2171 =
                      let uu____2172 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2172
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2170 uu____2171 msg))
  
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
  fun uu____2199  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___375_2217 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___375_2217.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___375_2217.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___375_2217.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___375_2217.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___375_2217.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___375_2217.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___375_2217.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___375_2217.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___375_2217.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___375_2217.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___375_2217.FStar_Tactics_Types.tac_verb_dbg);
              FStar_Tactics_Types.local_state =
                (uu___375_2217.FStar_Tactics_Types.local_state)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2241 = get_guard_policy ()  in
      bind uu____2241
        (fun old_pol  ->
           let uu____2247 = set_guard_policy pol  in
           bind uu____2247
             (fun uu____2251  ->
                bind t
                  (fun r  ->
                     let uu____2255 = set_guard_policy old_pol  in
                     bind uu____2255 (fun uu____2259  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2262 = let uu____2267 = cur_goal ()  in trytac uu____2267  in
  bind uu____2262
    (fun uu___346_2274  ->
       match uu___346_2274 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2280 = FStar_Options.peek ()  in ret uu____2280)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        mlog
          (fun uu____2302  ->
             let uu____2303 = FStar_TypeChecker_Rel.guard_to_string e g  in
             FStar_Util.print2 "Processing guard (%s:%s)\n" reason uu____2303)
          (fun uu____2306  ->
             let uu____2307 = add_implicits g.FStar_TypeChecker_Env.implicits
                in
             bind uu____2307
               (fun uu____2311  ->
                  bind getopts
                    (fun opts  ->
                       let uu____2315 =
                         let uu____2316 =
                           FStar_TypeChecker_Rel.simplify_guard e g  in
                         uu____2316.FStar_TypeChecker_Env.guard_f  in
                       match uu____2315 with
                       | FStar_TypeChecker_Common.Trivial  -> ret ()
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____2320 = istrivial e f  in
                           if uu____2320
                           then ret ()
                           else
                             bind get
                               (fun ps  ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop  ->
                                      ((let uu____2330 =
                                          let uu____2335 =
                                            let uu____2336 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g
                                               in
                                            FStar_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu____2336
                                             in
                                          (FStar_Errors.Warning_TacAdmit,
                                            uu____2335)
                                           in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu____2330);
                                       ret ())
                                  | FStar_Tactics_Types.Goal  ->
                                      mlog
                                        (fun uu____2339  ->
                                           let uu____2340 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu____2340)
                                        (fun uu____2343  ->
                                           let uu____2344 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2344
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___376_2351 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___376_2351.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___376_2351.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___376_2351.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_goals [goal1]))
                                  | FStar_Tactics_Types.SMT  ->
                                      mlog
                                        (fun uu____2354  ->
                                           let uu____2355 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Sending guard (%s:%s) to SMT goal\n"
                                             reason uu____2355)
                                        (fun uu____2358  ->
                                           let uu____2359 =
                                             mk_irrelevant_goal reason e f
                                               opts
                                              in
                                           bind uu____2359
                                             (fun goal  ->
                                                let goal1 =
                                                  let uu___377_2366 = goal
                                                     in
                                                  {
                                                    FStar_Tactics_Types.goal_main_env
                                                      =
                                                      (uu___377_2366.FStar_Tactics_Types.goal_main_env);
                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                      =
                                                      (uu___377_2366.FStar_Tactics_Types.goal_ctx_uvar);
                                                    FStar_Tactics_Types.opts
                                                      =
                                                      (uu___377_2366.FStar_Tactics_Types.opts);
                                                    FStar_Tactics_Types.is_guard
                                                      = true
                                                  }  in
                                                push_smt_goals [goal1]))
                                  | FStar_Tactics_Types.Force  ->
                                      mlog
                                        (fun uu____2369  ->
                                           let uu____2370 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g
                                              in
                                           FStar_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu____2370)
                                        (fun uu____2372  ->
                                           try
                                             (fun uu___379_2377  ->
                                                match () with
                                                | () ->
                                                    let uu____2380 =
                                                      let uu____2381 =
                                                        let uu____2382 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu____2382
                                                         in
                                                      Prims.op_Negation
                                                        uu____2381
                                                       in
                                                    if uu____2380
                                                    then
                                                      mlog
                                                        (fun uu____2387  ->
                                                           let uu____2388 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g
                                                              in
                                                           FStar_Util.print1
                                                             "guard = %s\n"
                                                             uu____2388)
                                                        (fun uu____2390  ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else ret ()) ()
                                           with
                                           | uu___378_2393 ->
                                               mlog
                                                 (fun uu____2398  ->
                                                    let uu____2399 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g
                                                       in
                                                    FStar_Util.print1
                                                      "guard = %s\n"
                                                      uu____2399)
                                                 (fun uu____2401  ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2411 =
      let uu____2414 = cur_goal ()  in
      bind uu____2414
        (fun goal  ->
           let uu____2420 =
             let uu____2429 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2429 t  in
           bind uu____2420
             (fun uu____2440  ->
                match uu____2440 with
                | (uu____2449,typ,uu____2451) -> ret typ))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2411
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2480 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2480 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2491  ->
    let uu____2494 = cur_goal ()  in
    bind uu____2494
      (fun goal  ->
         let uu____2500 =
           let uu____2501 = FStar_Tactics_Types.goal_env goal  in
           let uu____2502 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2501 uu____2502  in
         if uu____2500
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2506 =
              let uu____2507 = FStar_Tactics_Types.goal_env goal  in
              let uu____2508 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2507 uu____2508  in
            fail1 "Not a trivial goal: %s" uu____2506))
  
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
          let uu____2537 =
            let uu____2538 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2538.FStar_TypeChecker_Env.guard_f  in
          match uu____2537 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2546 = istrivial e f  in
              if uu____2546
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2554 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2554
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___380_2564 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___380_2564.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___380_2564.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___380_2564.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2571  ->
    let uu____2574 = cur_goal ()  in
    bind uu____2574
      (fun g  ->
         let uu____2580 = is_irrelevant g  in
         if uu____2580
         then bind __dismiss (fun uu____2584  -> add_smt_goals [g])
         else
           (let uu____2586 =
              let uu____2587 = FStar_Tactics_Types.goal_env g  in
              let uu____2588 = FStar_Tactics_Types.goal_type g  in
              tts uu____2587 uu____2588  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2586))
  
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
             let uu____2637 =
               try
                 (fun uu___385_2660  ->
                    match () with
                    | () ->
                        let uu____2671 =
                          let uu____2680 = FStar_BigInt.to_int_fs n1  in
                          FStar_List.splitAt uu____2680
                            p.FStar_Tactics_Types.goals
                           in
                        ret uu____2671) ()
               with | uu___384_2690 -> fail "divide: not enough goals"  in
             bind uu____2637
               (fun uu____2726  ->
                  match uu____2726 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___381_2752 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___381_2752.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___381_2752.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___381_2752.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___381_2752.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___381_2752.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___381_2752.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___381_2752.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___381_2752.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___381_2752.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___381_2752.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (uu___381_2752.FStar_Tactics_Types.local_state)
                        }  in
                      let uu____2753 = set lp  in
                      bind uu____2753
                        (fun uu____2761  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___382_2777 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___382_2777.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___382_2777.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___382_2777.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___382_2777.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___382_2777.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___382_2777.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___382_2777.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___382_2777.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___382_2777.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___382_2777.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (uu___382_2777.FStar_Tactics_Types.local_state)
                                       }  in
                                     let uu____2778 = set rp  in
                                     bind uu____2778
                                       (fun uu____2786  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___383_2802 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___383_2802.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (uu___383_2802.FStar_Tactics_Types.local_state)
                                                      }  in
                                                    let uu____2803 = set p'
                                                       in
                                                    bind uu____2803
                                                      (fun uu____2811  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2817 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2838 = divide FStar_BigInt.one f idtac  in
    bind uu____2838
      (fun uu____2851  -> match uu____2851 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2888::uu____2889 ->
             let uu____2892 =
               let uu____2901 = map tau  in
               divide FStar_BigInt.one tau uu____2901  in
             bind uu____2892
               (fun uu____2919  ->
                  match uu____2919 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2960 =
        bind t1
          (fun uu____2965  ->
             let uu____2966 = map t2  in
             bind uu____2966 (fun uu____2974  -> ret ()))
         in
      focus uu____2960
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2983  ->
    let uu____2986 =
      let uu____2989 = cur_goal ()  in
      bind uu____2989
        (fun goal  ->
           let uu____2998 =
             let uu____3005 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3005  in
           match uu____2998 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3014 =
                 let uu____3015 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3015  in
               if uu____3014
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3020 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3020 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3034 = new_uvar "intro" env' typ'  in
                  bind uu____3034
                    (fun uu____3050  ->
                       match uu____3050 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3074 = set_solution goal sol  in
                           bind uu____3074
                             (fun uu____3080  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3082 =
                                  let uu____3085 = bnorm_goal g  in
                                  replace_cur uu____3085  in
                                bind uu____3082 (fun uu____3087  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3092 =
                 let uu____3093 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3094 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3093 uu____3094  in
               fail1 "goal is not an arrow (%s)" uu____3092)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2986
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3109  ->
    let uu____3116 = cur_goal ()  in
    bind uu____3116
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3133 =
            let uu____3140 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3140  in
          match uu____3133 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3153 =
                let uu____3154 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3154  in
              if uu____3153
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3167 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3167
                    in
                 let bs =
                   let uu____3177 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3177; b]  in
                 let env' =
                   let uu____3203 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3203 bs  in
                 let uu____3204 =
                   let uu____3211 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3211  in
                 bind uu____3204
                   (fun uu____3230  ->
                      match uu____3230 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3244 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3247 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3244
                              FStar_Parser_Const.effect_Tot_lid uu____3247 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3265 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3265 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3287 =
                                   let uu____3288 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3288.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3287
                                  in
                               let uu____3301 = set_solution goal tm  in
                               bind uu____3301
                                 (fun uu____3310  ->
                                    let uu____3311 =
                                      let uu____3314 =
                                        bnorm_goal
                                          (let uu___386_3317 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___386_3317.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___386_3317.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___386_3317.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3314  in
                                    bind uu____3311
                                      (fun uu____3324  ->
                                         let uu____3325 =
                                           let uu____3330 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3330, b)  in
                                         ret uu____3325)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3339 =
                let uu____3340 = FStar_Tactics_Types.goal_env goal  in
                let uu____3341 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3340 uu____3341  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3339))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3359 = cur_goal ()  in
    bind uu____3359
      (fun goal  ->
         mlog
           (fun uu____3366  ->
              let uu____3367 =
                let uu____3368 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3368  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3367)
           (fun uu____3373  ->
              let steps =
                let uu____3377 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3377
                 in
              let t =
                let uu____3381 = FStar_Tactics_Types.goal_env goal  in
                let uu____3382 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3381 uu____3382  in
              let uu____3383 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3383))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3407 =
          mlog
            (fun uu____3412  ->
               let uu____3413 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3413)
            (fun uu____3415  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3421 -> g.FStar_Tactics_Types.opts
                      | uu____3424 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3429  ->
                         let uu____3430 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3430)
                      (fun uu____3433  ->
                         let uu____3434 = __tc e t  in
                         bind uu____3434
                           (fun uu____3455  ->
                              match uu____3455 with
                              | (t1,uu____3465,uu____3466) ->
                                  let steps =
                                    let uu____3470 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3470
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3407
  
let (refine_intro : unit -> unit tac) =
  fun uu____3484  ->
    let uu____3487 =
      let uu____3490 = cur_goal ()  in
      bind uu____3490
        (fun g  ->
           let uu____3497 =
             let uu____3508 = FStar_Tactics_Types.goal_env g  in
             let uu____3509 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3508 uu____3509
              in
           match uu____3497 with
           | (uu____3512,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3537 =
                 let uu____3542 =
                   let uu____3547 =
                     let uu____3548 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3548]  in
                   FStar_Syntax_Subst.open_term uu____3547 phi  in
                 match uu____3542 with
                 | (bvs,phi1) ->
                     let uu____3573 =
                       let uu____3574 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3574  in
                     (uu____3573, phi1)
                  in
               (match uu____3537 with
                | (bv1,phi1) ->
                    let uu____3593 =
                      let uu____3596 = FStar_Tactics_Types.goal_env g  in
                      let uu____3597 =
                        let uu____3598 =
                          let uu____3601 =
                            let uu____3602 =
                              let uu____3609 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3609)  in
                            FStar_Syntax_Syntax.NT uu____3602  in
                          [uu____3601]  in
                        FStar_Syntax_Subst.subst uu____3598 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3596
                        uu____3597 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3593
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3617  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3487
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3636 = cur_goal ()  in
      bind uu____3636
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3644 = FStar_Tactics_Types.goal_env goal  in
               let uu____3645 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3644 uu____3645
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3647 = __tc env t  in
           bind uu____3647
             (fun uu____3666  ->
                match uu____3666 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3681  ->
                         let uu____3682 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3683 =
                           let uu____3684 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3684
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3682 uu____3683)
                      (fun uu____3687  ->
                         let uu____3688 =
                           let uu____3691 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3691 guard  in
                         bind uu____3688
                           (fun uu____3693  ->
                              mlog
                                (fun uu____3697  ->
                                   let uu____3698 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3699 =
                                     let uu____3700 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3700
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3698 uu____3699)
                                (fun uu____3703  ->
                                   let uu____3704 =
                                     let uu____3707 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3708 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3707 typ uu____3708  in
                                   bind uu____3704
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3714 =
                                             let uu____3715 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3715 t1  in
                                           let uu____3716 =
                                             let uu____3717 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3717 typ  in
                                           let uu____3718 =
                                             let uu____3719 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3720 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3719 uu____3720  in
                                           let uu____3721 =
                                             let uu____3722 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3723 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3722 uu____3723  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3714 uu____3716 uu____3718
                                             uu____3721)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3738 =
        mlog
          (fun uu____3743  ->
             let uu____3744 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3744)
          (fun uu____3747  ->
             let uu____3748 =
               let uu____3755 = __exact_now set_expected_typ1 tm  in
               catch uu____3755  in
             bind uu____3748
               (fun uu___348_3764  ->
                  match uu___348_3764 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3774  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3777  ->
                           let uu____3778 =
                             let uu____3785 =
                               let uu____3788 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3788
                                 (fun uu____3793  ->
                                    let uu____3794 = refine_intro ()  in
                                    bind uu____3794
                                      (fun uu____3798  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             catch uu____3785  in
                           bind uu____3778
                             (fun uu___347_3805  ->
                                match uu___347_3805 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3813 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3738
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3863 = f x  in
          bind uu____3863
            (fun y  ->
               let uu____3871 = mapM f xs  in
               bind uu____3871 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3942 = do_unify e ty1 ty2  in
          bind uu____3942
            (fun uu___349_3954  ->
               if uu___349_3954
               then ret acc
               else
                 (let uu____3973 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3973 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3994 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3995 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3994
                        uu____3995
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____4010 =
                        let uu____4011 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____4011  in
                      if uu____4010
                      then fail "Codomain is effectful"
                      else
                        (let uu____4031 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____4031
                           (fun uu____4057  ->
                              match uu____4057 with
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
      let uu____4143 =
        mlog
          (fun uu____4148  ->
             let uu____4149 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4149)
          (fun uu____4152  ->
             let uu____4153 = cur_goal ()  in
             bind uu____4153
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4161 = __tc e tm  in
                  bind uu____4161
                    (fun uu____4182  ->
                       match uu____4182 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4195 =
                             let uu____4206 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4206  in
                           bind uu____4195
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4249  ->
                                       fun w  ->
                                         match uu____4249 with
                                         | (uvt,q,uu____4267) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4299 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4316  ->
                                       fun s  ->
                                         match uu____4316 with
                                         | (uu____4328,uu____4329,uv) ->
                                             let uu____4331 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4331) uvs uu____4299
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4340 = solve' goal w  in
                                bind uu____4340
                                  (fun uu____4345  ->
                                     let uu____4346 =
                                       mapM
                                         (fun uu____4363  ->
                                            match uu____4363 with
                                            | (uvt,q,uv) ->
                                                let uu____4375 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4375 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4380 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4381 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4381
                                                     then ret ()
                                                     else
                                                       (let uu____4385 =
                                                          let uu____4388 =
                                                            bnorm_goal
                                                              (let uu___387_4391
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___387_4391.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___387_4391.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4388]  in
                                                        add_goals uu____4385)))
                                         uvs
                                        in
                                     bind uu____4346
                                       (fun uu____4395  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4143
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4420 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4420
    then
      let uu____4427 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4442 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4495 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4427 with
      | (pre,post) ->
          let post1 =
            let uu____4527 =
              let uu____4538 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4538]  in
            FStar_Syntax_Util.mk_app post uu____4527  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4568 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4568
       then
         let uu____4575 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4575
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4608 =
      let uu____4611 =
        bind get
          (fun ps  ->
             mlog
               (fun uu____4618  ->
                  let uu____4619 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4619)
               (fun uu____4623  ->
                  let is_unit_t t =
                    let uu____4630 =
                      let uu____4631 = FStar_Syntax_Subst.compress t  in
                      uu____4631.FStar_Syntax_Syntax.n  in
                    match uu____4630 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.unit_lid
                        -> true
                    | uu____4635 -> false  in
                  let uu____4636 = cur_goal ()  in
                  bind uu____4636
                    (fun goal  ->
                       let uu____4642 =
                         let uu____4651 = FStar_Tactics_Types.goal_env goal
                            in
                         __tc uu____4651 tm  in
                       bind uu____4642
                         (fun uu____4666  ->
                            match uu____4666 with
                            | (tm1,t,guard) ->
                                let uu____4678 =
                                  FStar_Syntax_Util.arrow_formals_comp t  in
                                (match uu____4678 with
                                 | (bs,comp) ->
                                     let uu____4711 = lemma_or_sq comp  in
                                     (match uu____4711 with
                                      | FStar_Pervasives_Native.None  ->
                                          fail
                                            "not a lemma or squashed function"
                                      | FStar_Pervasives_Native.Some
                                          (pre,post) ->
                                          let uu____4730 =
                                            FStar_List.fold_left
                                              (fun uu____4778  ->
                                                 fun uu____4779  ->
                                                   match (uu____4778,
                                                           uu____4779)
                                                   with
                                                   | ((uvs,guard1,subst1),
                                                      (b,aq)) ->
                                                       let b_t =
                                                         FStar_Syntax_Subst.subst
                                                           subst1
                                                           b.FStar_Syntax_Syntax.sort
                                                          in
                                                       let uu____4892 =
                                                         is_unit_t b_t  in
                                                       if uu____4892
                                                       then
                                                         (((FStar_Syntax_Util.exp_unit,
                                                             aq) :: uvs),
                                                           guard1,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b,
                                                                 FStar_Syntax_Util.exp_unit))
                                                           :: subst1))
                                                       else
                                                         (let uu____4930 =
                                                            let uu____4943 =
                                                              let uu____4944
                                                                =
                                                                FStar_Tactics_Types.goal_type
                                                                  goal
                                                                 in
                                                              uu____4944.FStar_Syntax_Syntax.pos
                                                               in
                                                            let uu____4947 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            FStar_TypeChecker_Util.new_implicit_var
                                                              "apply_lemma"
                                                              uu____4943
                                                              uu____4947 b_t
                                                             in
                                                          match uu____4930
                                                          with
                                                          | (u,uu____4965,g_u)
                                                              ->
                                                              let uu____4979
                                                                =
                                                                FStar_TypeChecker_Env.conj_guard
                                                                  guard1 g_u
                                                                 in
                                                              (((u, aq) ::
                                                                uvs),
                                                                uu____4979,
                                                                ((FStar_Syntax_Syntax.NT
                                                                    (b, u))
                                                                :: subst1))))
                                              ([], guard, []) bs
                                             in
                                          (match uu____4730 with
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
                                               let uu____5058 =
                                                 let uu____5061 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal
                                                    in
                                                 let uu____5062 =
                                                   FStar_Syntax_Util.mk_squash
                                                     FStar_Syntax_Syntax.U_zero
                                                     post1
                                                    in
                                                 let uu____5063 =
                                                   FStar_Tactics_Types.goal_type
                                                     goal
                                                    in
                                                 do_unify uu____5061
                                                   uu____5062 uu____5063
                                                  in
                                               bind uu____5058
                                                 (fun b  ->
                                                    if Prims.op_Negation b
                                                    then
                                                      let uu____5071 =
                                                        let uu____5072 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        tts uu____5072 tm1
                                                         in
                                                      let uu____5073 =
                                                        let uu____5074 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5075 =
                                                          FStar_Syntax_Util.mk_squash
                                                            FStar_Syntax_Syntax.U_zero
                                                            post1
                                                           in
                                                        tts uu____5074
                                                          uu____5075
                                                         in
                                                      let uu____5076 =
                                                        let uu____5077 =
                                                          FStar_Tactics_Types.goal_env
                                                            goal
                                                           in
                                                        let uu____5078 =
                                                          FStar_Tactics_Types.goal_type
                                                            goal
                                                           in
                                                        tts uu____5077
                                                          uu____5078
                                                         in
                                                      fail3
                                                        "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                        uu____5071 uu____5073
                                                        uu____5076
                                                    else
                                                      (let uu____5080 =
                                                         add_implicits
                                                           implicits.FStar_TypeChecker_Env.implicits
                                                          in
                                                       bind uu____5080
                                                         (fun uu____5085  ->
                                                            let uu____5086 =
                                                              solve' goal
                                                                FStar_Syntax_Util.exp_unit
                                                               in
                                                            bind uu____5086
                                                              (fun uu____5094
                                                                  ->
                                                                 let is_free_uvar
                                                                   uv t1 =
                                                                   let free_uvars
                                                                    =
                                                                    let uu____5119
                                                                    =
                                                                    let uu____5122
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                    FStar_Util.set_elements
                                                                    uu____5122
                                                                     in
                                                                    FStar_List.map
                                                                    (fun x 
                                                                    ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu____5119
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
                                                                    let uu____5157
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu____5157)
                                                                    goals
                                                                    in
                                                                 let checkone
                                                                   t1 goals =
                                                                   let uu____5173
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1  in
                                                                   match uu____5173
                                                                   with
                                                                   | 
                                                                   (hd1,uu____5191)
                                                                    ->
                                                                    (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5217)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu____5234
                                                                    -> false)
                                                                    in
                                                                 let uu____5235
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
                                                                    let uu____5265
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5265
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5287)
                                                                    ->
                                                                    let uu____5312
                                                                    =
                                                                    let uu____5313
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5313.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5312
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5321)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___388_5341
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___388_5341.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___388_5341.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___388_5341.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    [goal1]
                                                                    | 
                                                                    uu____5344
                                                                    ->
                                                                    mlog
                                                                    (fun
                                                                    uu____5350
                                                                     ->
                                                                    let uu____5351
                                                                    =
                                                                    FStar_Syntax_Print.uvar_to_string
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                                                     in
                                                                    let uu____5352
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.print2
                                                                    "apply_lemma: arg %s unified to (%s)\n"
                                                                    uu____5351
                                                                    uu____5352)
                                                                    (fun
                                                                    uu____5357
                                                                     ->
                                                                    let env =
                                                                    let uu___389_5359
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___389_5359.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term'
                                                                    true env
                                                                    term
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let uu____5361
                                                                    =
                                                                    let uu____5364
                                                                    =
                                                                    if
                                                                    ps.FStar_Tactics_Types.tac_verb_dbg
                                                                    then
                                                                    let uu____5365
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    ctx_uvar
                                                                     in
                                                                    let uu____5366
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    term  in
                                                                    FStar_Util.format2
                                                                    "apply_lemma solved arg %s to %s\n"
                                                                    uu____5365
                                                                    uu____5366
                                                                    else
                                                                    "apply_lemma solved arg"
                                                                     in
                                                                    let uu____5368
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    uu____5364
                                                                    uu____5368
                                                                    g_typ  in
                                                                    bind
                                                                    uu____5361
                                                                    (fun
                                                                    uu____5372
                                                                     ->
                                                                    ret [])))))
                                                                    in
                                                                 bind
                                                                   uu____5235
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
                                                                    let uu____5434
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5434
                                                                    then
                                                                    let uu____5437
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5437
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
                                                                    let uu____5451
                                                                    =
                                                                    let uu____5452
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5452
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5451)
                                                                    sub_goals1
                                                                     in
                                                                    let uu____5453
                                                                    =
                                                                    let uu____5456
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5456
                                                                    guard  in
                                                                    bind
                                                                    uu____5453
                                                                    (fun
                                                                    uu____5459
                                                                     ->
                                                                    let uu____5460
                                                                    =
                                                                    let uu____5463
                                                                    =
                                                                    let uu____5464
                                                                    =
                                                                    let uu____5465
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5466
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5465
                                                                    uu____5466
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5464
                                                                     in
                                                                    if
                                                                    uu____5463
                                                                    then
                                                                    let uu____5469
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5469
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5460
                                                                    (fun
                                                                    uu____5472
                                                                     ->
                                                                    add_goals
                                                                    sub_goals2))))))))))))))
         in
      focus uu____4611  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4608
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5494 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5494 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5504::(e1,uu____5506)::(e2,uu____5508)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5569 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5593 = destruct_eq' typ  in
    match uu____5593 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5623 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5623 with
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
        let uu____5685 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5685 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5733 = aux e'  in
               FStar_Util.map_opt uu____5733
                 (fun uu____5757  ->
                    match uu____5757 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5778 = aux e  in
      FStar_Util.map_opt uu____5778
        (fun uu____5802  ->
           match uu____5802 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5869 =
            let uu____5878 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5878  in
          FStar_Util.map_opt uu____5869
            (fun uu____5893  ->
               match uu____5893 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___390_5912 = bv  in
                     let uu____5913 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___390_5912.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___390_5912.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5913
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___391_5921 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5922 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5931 =
                       let uu____5934 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5934  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___391_5921.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5922;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5931;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___391_5921.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___391_5921.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___391_5921.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___392_5935 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___392_5935.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___392_5935.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___392_5935.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5945 =
      let uu____5948 = cur_goal ()  in
      bind uu____5948
        (fun goal  ->
           let uu____5956 = h  in
           match uu____5956 with
           | (bv,uu____5960) ->
               mlog
                 (fun uu____5968  ->
                    let uu____5969 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5970 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5969
                      uu____5970)
                 (fun uu____5973  ->
                    let uu____5974 =
                      let uu____5983 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5983  in
                    match uu____5974 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6004 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6004 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6019 =
                               let uu____6020 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6020.FStar_Syntax_Syntax.n  in
                             (match uu____6019 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___393_6037 = bv1  in
                                    let uu____6038 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___393_6037.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___393_6037.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6038
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___394_6046 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6047 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6056 =
                                      let uu____6059 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6059
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___394_6046.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6047;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6056;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___394_6046.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___394_6046.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___394_6046.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___395_6062 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___395_6062.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___395_6062.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___395_6062.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6063 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6064 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5945
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6089 =
        let uu____6092 = cur_goal ()  in
        bind uu____6092
          (fun goal  ->
             let uu____6103 = b  in
             match uu____6103 with
             | (bv,uu____6107) ->
                 let bv' =
                   let uu____6113 =
                     let uu___396_6114 = bv  in
                     let uu____6115 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6115;
                       FStar_Syntax_Syntax.index =
                         (uu___396_6114.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___396_6114.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6113  in
                 let s1 =
                   let uu____6119 =
                     let uu____6120 =
                       let uu____6127 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6127)  in
                     FStar_Syntax_Syntax.NT uu____6120  in
                   [uu____6119]  in
                 let uu____6132 = subst_goal bv bv' s1 goal  in
                 (match uu____6132 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6089
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6151 =
      let uu____6154 = cur_goal ()  in
      bind uu____6154
        (fun goal  ->
           let uu____6163 = b  in
           match uu____6163 with
           | (bv,uu____6167) ->
               let uu____6172 =
                 let uu____6181 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6181  in
               (match uu____6172 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6202 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6202 with
                     | (ty,u) ->
                         let uu____6211 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6211
                           (fun uu____6229  ->
                              match uu____6229 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___397_6239 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___397_6239.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___397_6239.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6243 =
                                      let uu____6244 =
                                        let uu____6251 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6251)  in
                                      FStar_Syntax_Syntax.NT uu____6244  in
                                    [uu____6243]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___398_6263 = b1  in
                                         let uu____6264 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___398_6263.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___398_6263.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6264
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6271  ->
                                       let new_goal =
                                         let uu____6273 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6274 =
                                           let uu____6275 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6275
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6273 uu____6274
                                          in
                                       let uu____6276 = add_goals [new_goal]
                                          in
                                       bind uu____6276
                                         (fun uu____6281  ->
                                            let uu____6282 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6282
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6151
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6305 =
        let uu____6308 = cur_goal ()  in
        bind uu____6308
          (fun goal  ->
             let uu____6317 = b  in
             match uu____6317 with
             | (bv,uu____6321) ->
                 let uu____6326 =
                   let uu____6335 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6335  in
                 (match uu____6326 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6359 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6359
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___399_6364 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___399_6364.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___399_6364.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6366 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6366))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6305
  
let (revert : unit -> unit tac) =
  fun uu____6377  ->
    let uu____6380 = cur_goal ()  in
    bind uu____6380
      (fun goal  ->
         let uu____6386 =
           let uu____6393 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6393  in
         match uu____6386 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6409 =
                 let uu____6412 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6412  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6409
                in
             let uu____6427 = new_uvar "revert" env' typ'  in
             bind uu____6427
               (fun uu____6442  ->
                  match uu____6442 with
                  | (r,u_r) ->
                      let uu____6451 =
                        let uu____6454 =
                          let uu____6455 =
                            let uu____6456 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6456.FStar_Syntax_Syntax.pos  in
                          let uu____6459 =
                            let uu____6464 =
                              let uu____6465 =
                                let uu____6474 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6474  in
                              [uu____6465]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6464  in
                          uu____6459 FStar_Pervasives_Native.None uu____6455
                           in
                        set_solution goal uu____6454  in
                      bind uu____6451
                        (fun uu____6495  ->
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
      let uu____6507 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6507
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6522 = cur_goal ()  in
    bind uu____6522
      (fun goal  ->
         mlog
           (fun uu____6530  ->
              let uu____6531 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6532 =
                let uu____6533 =
                  let uu____6534 =
                    let uu____6543 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6543  in
                  FStar_All.pipe_right uu____6534 FStar_List.length  in
                FStar_All.pipe_right uu____6533 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6531 uu____6532)
           (fun uu____6560  ->
              let uu____6561 =
                let uu____6570 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6570  in
              match uu____6561 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6609 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6609
                        then
                          let uu____6612 =
                            let uu____6613 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6613
                             in
                          fail uu____6612
                        else check1 bvs2
                     in
                  let uu____6615 =
                    let uu____6616 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6616  in
                  if uu____6615
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6620 = check1 bvs  in
                     bind uu____6620
                       (fun uu____6626  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6628 =
                            let uu____6635 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6635  in
                          bind uu____6628
                            (fun uu____6644  ->
                               match uu____6644 with
                               | (ut,uvar_ut) ->
                                   let uu____6653 = set_solution goal ut  in
                                   bind uu____6653
                                     (fun uu____6658  ->
                                        let uu____6659 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6659))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6666  ->
    let uu____6669 = cur_goal ()  in
    bind uu____6669
      (fun goal  ->
         let uu____6675 =
           let uu____6682 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6682  in
         match uu____6675 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6690) ->
             let uu____6695 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6695)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6705 = cur_goal ()  in
    bind uu____6705
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6715 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6715  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6718  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6728 = cur_goal ()  in
    bind uu____6728
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6738 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6738  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6741  -> add_goals [g']))
  
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
            let uu____6781 = FStar_Syntax_Subst.compress t  in
            uu____6781.FStar_Syntax_Syntax.n  in
          let uu____6784 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___403_6790 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___403_6790.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___403_6790.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6784
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6806 =
                   let uu____6807 = FStar_Syntax_Subst.compress t1  in
                   uu____6807.FStar_Syntax_Syntax.n  in
                 match uu____6806 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6838 = ff hd1  in
                     bind uu____6838
                       (fun hd2  ->
                          let fa uu____6864 =
                            match uu____6864 with
                            | (a,q) ->
                                let uu____6885 = ff a  in
                                bind uu____6885 (fun a1  -> ret (a1, q))
                             in
                          let uu____6904 = mapM fa args  in
                          bind uu____6904
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6986 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6986 with
                      | (bs1,t') ->
                          let uu____6995 =
                            let uu____6998 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6998 t'  in
                          bind uu____6995
                            (fun t''  ->
                               let uu____7002 =
                                 let uu____7003 =
                                   let uu____7022 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7031 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7022, uu____7031, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7003  in
                               ret uu____7002))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7106 = ff hd1  in
                     bind uu____7106
                       (fun hd2  ->
                          let ffb br =
                            let uu____7121 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7121 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7153 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7153  in
                                let uu____7154 = ff1 e  in
                                bind uu____7154
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7169 = mapM ffb brs  in
                          bind uu____7169
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7213;
                          FStar_Syntax_Syntax.lbtyp = uu____7214;
                          FStar_Syntax_Syntax.lbeff = uu____7215;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7217;
                          FStar_Syntax_Syntax.lbpos = uu____7218;_}::[]),e)
                     ->
                     let lb =
                       let uu____7243 =
                         let uu____7244 = FStar_Syntax_Subst.compress t1  in
                         uu____7244.FStar_Syntax_Syntax.n  in
                       match uu____7243 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7248) -> lb
                       | uu____7261 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7270 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7270
                         (fun def1  ->
                            ret
                              (let uu___400_7276 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___400_7276.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___400_7276.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___400_7276.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___400_7276.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___400_7276.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___400_7276.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7277 = fflb lb  in
                     bind uu____7277
                       (fun lb1  ->
                          let uu____7287 =
                            let uu____7292 =
                              let uu____7293 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7293]  in
                            FStar_Syntax_Subst.open_term uu____7292 e  in
                          match uu____7287 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7323 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7323  in
                              let uu____7324 = ff1 e1  in
                              bind uu____7324
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7365 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7365
                         (fun def  ->
                            ret
                              (let uu___401_7371 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___401_7371.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___401_7371.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___401_7371.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___401_7371.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___401_7371.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___401_7371.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7372 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7372 with
                      | (lbs1,e1) ->
                          let uu____7387 = mapM fflb lbs1  in
                          bind uu____7387
                            (fun lbs2  ->
                               let uu____7399 = ff e1  in
                               bind uu____7399
                                 (fun e2  ->
                                    let uu____7407 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7407 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7475 = ff t2  in
                     bind uu____7475
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7506 = ff t2  in
                     bind uu____7506
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7513 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___402_7520 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___402_7520.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___402_7520.FStar_Syntax_Syntax.vars)
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
            let uu____7557 =
              FStar_TypeChecker_TcTerm.tc_term
                (let uu___404_7566 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___404_7566.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___404_7566.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___404_7566.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___404_7566.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___404_7566.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___404_7566.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___404_7566.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___404_7566.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___404_7566.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___404_7566.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___404_7566.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___404_7566.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___404_7566.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___404_7566.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___404_7566.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___404_7566.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___404_7566.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___404_7566.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___404_7566.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___404_7566.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax = true;
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___404_7566.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___404_7566.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___404_7566.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___404_7566.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___404_7566.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___404_7566.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___404_7566.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___404_7566.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___404_7566.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___404_7566.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___404_7566.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___404_7566.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___404_7566.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___404_7566.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___404_7566.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___404_7566.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___404_7566.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___404_7566.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___404_7566.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___404_7566.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___404_7566.FStar_TypeChecker_Env.nbe)
                 }) t
               in
            match uu____7557 with
            | (t1,lcomp,g) ->
                let uu____7572 =
                  (let uu____7575 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7575) ||
                    (let uu____7577 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7577)
                   in
                if uu____7572
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7585 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7585
                       (fun uu____7601  ->
                          match uu____7601 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7614  ->
                                    let uu____7615 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7616 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7615 uu____7616);
                               (let uu____7617 =
                                  let uu____7620 =
                                    let uu____7621 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7621 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7620
                                    opts
                                   in
                                bind uu____7617
                                  (fun uu____7624  ->
                                     let uu____7625 =
                                       bind tau
                                         (fun uu____7631  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7637  ->
                                                 let uu____7638 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7639 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7638 uu____7639);
                                            ret ut1)
                                        in
                                     focus uu____7625))))
                      in
                   let uu____7640 = catch rewrite_eq  in
                   bind uu____7640
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
          let uu____7838 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7838
            (fun t1  ->
               let uu____7846 =
                 f env
                   (let uu___407_7855 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___407_7855.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___407_7855.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7846
                 (fun uu____7871  ->
                    match uu____7871 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7894 =
                               let uu____7895 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7895.FStar_Syntax_Syntax.n  in
                             match uu____7894 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7932 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7932
                                   (fun uu____7957  ->
                                      match uu____7957 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7973 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7973
                                            (fun uu____8000  ->
                                               match uu____8000 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___405_8030 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___405_8030.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___405_8030.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8072 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8072 with
                                  | (bs1,t') ->
                                      let uu____8087 =
                                        let uu____8094 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8094 ctrl1 t'
                                         in
                                      bind uu____8087
                                        (fun uu____8112  ->
                                           match uu____8112 with
                                           | (t'',ctrl2) ->
                                               let uu____8127 =
                                                 let uu____8134 =
                                                   let uu___406_8137 = t4  in
                                                   let uu____8140 =
                                                     let uu____8141 =
                                                       let uu____8160 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8169 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8160,
                                                         uu____8169, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8141
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8140;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___406_8137.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___406_8137.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8134, ctrl2)  in
                                               ret uu____8127))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8222 -> ret (t3, ctrl1))))

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
              let uu____8269 = ctrl_tac_fold f env ctrl t  in
              bind uu____8269
                (fun uu____8293  ->
                   match uu____8293 with
                   | (t1,ctrl1) ->
                       let uu____8308 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8308
                         (fun uu____8335  ->
                            match uu____8335 with
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
              let uu____8419 =
                let uu____8426 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8426
                  (fun uu____8435  ->
                     let uu____8436 = ctrl t1  in
                     bind uu____8436
                       (fun res  ->
                          let uu____8459 = trivial ()  in
                          bind uu____8459 (fun uu____8467  -> ret res)))
                 in
              bind uu____8419
                (fun uu____8483  ->
                   match uu____8483 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8507 =
                            FStar_TypeChecker_TcTerm.tc_term
                              (let uu___408_8516 = env  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___408_8516.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___408_8516.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___408_8516.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___408_8516.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___408_8516.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___408_8516.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___408_8516.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___408_8516.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___408_8516.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___408_8516.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___408_8516.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___408_8516.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___408_8516.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___408_8516.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___408_8516.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___408_8516.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___408_8516.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___408_8516.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___408_8516.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___408_8516.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax = true;
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___408_8516.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___408_8516.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___408_8516.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___408_8516.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___408_8516.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___408_8516.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___408_8516.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___408_8516.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___408_8516.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___408_8516.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___408_8516.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___408_8516.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___408_8516.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___408_8516.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___408_8516.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___408_8516.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___408_8516.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___408_8516.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___408_8516.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.dep_graph =
                                   (uu___408_8516.FStar_TypeChecker_Env.dep_graph);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___408_8516.FStar_TypeChecker_Env.nbe)
                               }) t1
                             in
                          match uu____8507 with
                          | (t2,lcomp,g) ->
                              let uu____8526 =
                                (let uu____8529 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8529) ||
                                  (let uu____8531 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8531)
                                 in
                              if uu____8526
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8544 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8544
                                   (fun uu____8564  ->
                                      match uu____8564 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8581  ->
                                                let uu____8582 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8583 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8582 uu____8583);
                                           (let uu____8584 =
                                              let uu____8587 =
                                                let uu____8588 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8588 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8587 opts
                                               in
                                            bind uu____8584
                                              (fun uu____8595  ->
                                                 let uu____8596 =
                                                   bind rewriter
                                                     (fun uu____8610  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8616  ->
                                                             let uu____8617 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8618 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8617
                                                               uu____8618);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8596)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8659 =
        bind get
          (fun ps  ->
             let uu____8669 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8669 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8706  ->
                       let uu____8707 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8707);
                  bind dismiss_all
                    (fun uu____8710  ->
                       let uu____8711 =
                         let uu____8718 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8718
                           keepGoing gt1
                          in
                       bind uu____8711
                         (fun uu____8730  ->
                            match uu____8730 with
                            | (gt',uu____8738) ->
                                (log ps
                                   (fun uu____8742  ->
                                      let uu____8743 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8743);
                                 (let uu____8744 = push_goals gs  in
                                  bind uu____8744
                                    (fun uu____8749  ->
                                       let uu____8750 =
                                         let uu____8753 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8753]  in
                                       add_goals uu____8750)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8659
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8776 =
        bind get
          (fun ps  ->
             let uu____8786 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8786 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8823  ->
                       let uu____8824 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8824);
                  bind dismiss_all
                    (fun uu____8827  ->
                       let uu____8828 =
                         let uu____8831 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8831 gt1
                          in
                       bind uu____8828
                         (fun gt'  ->
                            log ps
                              (fun uu____8839  ->
                                 let uu____8840 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8840);
                            (let uu____8841 = push_goals gs  in
                             bind uu____8841
                               (fun uu____8846  ->
                                  let uu____8847 =
                                    let uu____8850 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8850]  in
                                  add_goals uu____8847))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8776
  
let (trefl : unit -> unit tac) =
  fun uu____8861  ->
    let uu____8864 =
      let uu____8867 = cur_goal ()  in
      bind uu____8867
        (fun g  ->
           let uu____8885 =
             let uu____8890 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8890  in
           match uu____8885 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8898 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8898 with
                | (hd1,args) ->
                    let uu____8937 =
                      let uu____8950 =
                        let uu____8951 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8951.FStar_Syntax_Syntax.n  in
                      (uu____8950, args)  in
                    (match uu____8937 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8965::(l,uu____8967)::(r,uu____8969)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9016 =
                           let uu____9019 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9019 l r  in
                         bind uu____9016
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9026 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9026 l
                                    in
                                 let r1 =
                                   let uu____9028 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9028 r
                                    in
                                 let uu____9029 =
                                   let uu____9032 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9032 l1 r1  in
                                 bind uu____9029
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9038 =
                                           let uu____9039 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9039 l1  in
                                         let uu____9040 =
                                           let uu____9041 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9041 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9038 uu____9040))))
                     | (hd2,uu____9043) ->
                         let uu____9060 =
                           let uu____9061 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9061 t  in
                         fail1 "trefl: not an equality (%s)" uu____9060))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8864
  
let (dup : unit -> unit tac) =
  fun uu____9074  ->
    let uu____9077 = cur_goal ()  in
    bind uu____9077
      (fun g  ->
         let uu____9083 =
           let uu____9090 = FStar_Tactics_Types.goal_env g  in
           let uu____9091 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9090 uu____9091  in
         bind uu____9083
           (fun uu____9100  ->
              match uu____9100 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___409_9110 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___409_9110.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___409_9110.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___409_9110.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9113  ->
                       let uu____9114 =
                         let uu____9117 = FStar_Tactics_Types.goal_env g  in
                         let uu____9118 =
                           let uu____9119 =
                             let uu____9120 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9121 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9120
                               uu____9121
                              in
                           let uu____9122 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9123 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9119 uu____9122 u
                             uu____9123
                            in
                         add_irrelevant_goal "dup equation" uu____9117
                           uu____9118 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9114
                         (fun uu____9126  ->
                            let uu____9127 = add_goals [g']  in
                            bind uu____9127 (fun uu____9131  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9138  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___410_9155 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___410_9155.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___410_9155.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___410_9155.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___410_9155.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___410_9155.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___410_9155.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___410_9155.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___410_9155.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___410_9155.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___410_9155.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___410_9155.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___410_9155.FStar_Tactics_Types.local_state)
                })
         | uu____9156 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9165  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___411_9178 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___411_9178.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___411_9178.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___411_9178.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___411_9178.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___411_9178.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___411_9178.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___411_9178.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___411_9178.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___411_9178.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___411_9178.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___411_9178.FStar_Tactics_Types.tac_verb_dbg);
                  FStar_Tactics_Types.local_state =
                    (uu___411_9178.FStar_Tactics_Types.local_state)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9185  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9192 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9212 =
      let uu____9219 = cur_goal ()  in
      bind uu____9219
        (fun g  ->
           let uu____9229 =
             let uu____9238 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9238 t  in
           bind uu____9229
             (fun uu____9266  ->
                match uu____9266 with
                | (t1,typ,guard) ->
                    let uu____9282 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9282 with
                     | (hd1,args) ->
                         let uu____9331 =
                           let uu____9346 =
                             let uu____9347 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9347.FStar_Syntax_Syntax.n  in
                           (uu____9346, args)  in
                         (match uu____9331 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9368)::(q,uu____9370)::[]) when
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
                                let uu____9424 =
                                  let uu____9425 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9425
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9424
                                 in
                              let g2 =
                                let uu____9427 =
                                  let uu____9428 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9428
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9427
                                 in
                              bind __dismiss
                                (fun uu____9435  ->
                                   let uu____9436 = add_goals [g1; g2]  in
                                   bind uu____9436
                                     (fun uu____9445  ->
                                        let uu____9446 =
                                          let uu____9451 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9452 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9451, uu____9452)  in
                                        ret uu____9446))
                          | uu____9457 ->
                              let uu____9472 =
                                let uu____9473 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9473 typ  in
                              fail1 "Not a disjunction: %s" uu____9472))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9212
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9503 =
      let uu____9506 = cur_goal ()  in
      bind uu____9506
        (fun g  ->
           FStar_Options.push ();
           (let uu____9519 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9519);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___412_9526 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___412_9526.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___412_9526.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___412_9526.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9503
  
let (top_env : unit -> env tac) =
  fun uu____9538  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9551  ->
    let uu____9554 = cur_goal ()  in
    bind uu____9554
      (fun g  ->
         let uu____9560 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9560)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9569  ->
    let uu____9572 = cur_goal ()  in
    bind uu____9572
      (fun g  ->
         let uu____9578 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9578)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9587  ->
    let uu____9590 = cur_goal ()  in
    bind uu____9590
      (fun g  ->
         let uu____9596 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9596)
  
let (lax_on : unit -> Prims.bool tac) =
  fun uu____9605  ->
    let uu____9608 = cur_env ()  in
    bind uu____9608
      (fun e  ->
         let uu____9614 =
           (FStar_Options.lax ()) || e.FStar_TypeChecker_Env.lax  in
         ret uu____9614)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9629 =
        mlog
          (fun uu____9634  ->
             let uu____9635 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9635)
          (fun uu____9638  ->
             let uu____9639 = cur_goal ()  in
             bind uu____9639
               (fun goal  ->
                  let env =
                    let uu____9647 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9647 ty  in
                  let uu____9648 = __tc env tm  in
                  bind uu____9648
                    (fun uu____9667  ->
                       match uu____9667 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9681  ->
                                let uu____9682 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9682)
                             (fun uu____9684  ->
                                mlog
                                  (fun uu____9687  ->
                                     let uu____9688 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9688)
                                  (fun uu____9691  ->
                                     let uu____9692 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9692
                                       (fun uu____9696  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9629
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9719 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9725 =
              let uu____9732 =
                let uu____9733 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9733
                 in
              new_uvar "uvar_env.2" env uu____9732  in
            bind uu____9725
              (fun uu____9749  ->
                 match uu____9749 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9719
        (fun typ  ->
           let uu____9761 = new_uvar "uvar_env" env typ  in
           bind uu____9761
             (fun uu____9775  -> match uu____9775 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9793 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9812 -> g.FStar_Tactics_Types.opts
             | uu____9815 -> FStar_Options.peek ()  in
           let uu____9818 = FStar_Syntax_Util.head_and_args t  in
           match uu____9818 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9838);
                FStar_Syntax_Syntax.pos = uu____9839;
                FStar_Syntax_Syntax.vars = uu____9840;_},uu____9841)
               ->
               let env1 =
                 let uu___413_9883 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___413_9883.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___413_9883.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___413_9883.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___413_9883.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___413_9883.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___413_9883.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___413_9883.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___413_9883.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___413_9883.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___413_9883.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___413_9883.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___413_9883.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___413_9883.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___413_9883.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___413_9883.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___413_9883.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___413_9883.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___413_9883.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___413_9883.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___413_9883.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___413_9883.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___413_9883.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___413_9883.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___413_9883.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___413_9883.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___413_9883.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___413_9883.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___413_9883.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___413_9883.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___413_9883.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___413_9883.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___413_9883.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___413_9883.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___413_9883.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___413_9883.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___413_9883.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___413_9883.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___413_9883.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___413_9883.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___413_9883.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___413_9883.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9885 =
                 let uu____9888 = bnorm_goal g  in [uu____9888]  in
               add_goals uu____9885
           | uu____9889 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9793
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9938 = if b then t2 else ret false  in
             bind uu____9938 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9949 = trytac comp  in
      bind uu____9949
        (fun uu___350_9957  ->
           match uu___350_9957 with
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
        let uu____9983 =
          bind get
            (fun ps  ->
               let uu____9989 = __tc e t1  in
               bind uu____9989
                 (fun uu____10009  ->
                    match uu____10009 with
                    | (t11,ty1,g1) ->
                        let uu____10021 = __tc e t2  in
                        bind uu____10021
                          (fun uu____10041  ->
                             match uu____10041 with
                             | (t21,ty2,g2) ->
                                 let uu____10053 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10053
                                   (fun uu____10058  ->
                                      let uu____10059 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10059
                                        (fun uu____10065  ->
                                           let uu____10066 =
                                             do_unify e ty1 ty2  in
                                           let uu____10069 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10066 uu____10069)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9983
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10102  ->
             let uu____10103 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10103
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
        (fun uu____10124  ->
           let uu____10125 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10125)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10135 =
      mlog
        (fun uu____10140  ->
           let uu____10141 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10141)
        (fun uu____10144  ->
           let uu____10145 = cur_goal ()  in
           bind uu____10145
             (fun g  ->
                let uu____10151 =
                  let uu____10160 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10160 ty  in
                bind uu____10151
                  (fun uu____10172  ->
                     match uu____10172 with
                     | (ty1,uu____10182,guard) ->
                         let uu____10184 =
                           let uu____10187 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10187 guard  in
                         bind uu____10184
                           (fun uu____10190  ->
                              let uu____10191 =
                                let uu____10194 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10195 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10194 uu____10195 ty1  in
                              bind uu____10191
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10201 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10201
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
                                        let uu____10207 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10208 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10207
                                          uu____10208
                                         in
                                      let nty =
                                        let uu____10210 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10210 ty1  in
                                      let uu____10211 =
                                        let uu____10214 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10214 ng nty  in
                                      bind uu____10211
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10220 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10220
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10135
  
let failwhen : 'a . Prims.bool -> Prims.string -> (unit -> 'a tac) -> 'a tac
  = fun b  -> fun msg  -> fun k  -> if b then fail msg else k () 
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      Prims.list tac)
  =
  fun s_tm  ->
    let uu____10283 =
      let uu____10292 = cur_goal ()  in
      bind uu____10292
        (fun g  ->
           let uu____10304 =
             let uu____10313 = FStar_Tactics_Types.goal_env g  in
             __tc uu____10313 s_tm  in
           bind uu____10304
             (fun uu____10331  ->
                match uu____10331 with
                | (s_tm1,s_ty,guard) ->
                    let uu____10349 =
                      let uu____10352 = FStar_Tactics_Types.goal_env g  in
                      proc_guard "destruct" uu____10352 guard  in
                    bind uu____10349
                      (fun uu____10364  ->
                         let uu____10365 =
                           FStar_Syntax_Util.head_and_args' s_ty  in
                         match uu____10365 with
                         | (h,args) ->
                             let uu____10410 =
                               let uu____10417 =
                                 let uu____10418 =
                                   FStar_Syntax_Subst.compress h  in
                                 uu____10418.FStar_Syntax_Syntax.n  in
                               match uu____10417 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____10433;
                                      FStar_Syntax_Syntax.vars = uu____10434;_},us)
                                   -> ret (fv, us)
                               | uu____10444 -> fail "type is not an fv"  in
                             bind uu____10410
                               (fun uu____10464  ->
                                  match uu____10464 with
                                  | (fv,a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv  in
                                      let uu____10480 =
                                        let uu____10483 =
                                          FStar_Tactics_Types.goal_env g  in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu____10483 t_lid
                                         in
                                      (match uu____10480 with
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
                                                  (fun uu____10532  ->
                                                     let uu____10533 =
                                                       FStar_Syntax_Subst.open_term
                                                         t_ps t_ty
                                                        in
                                                     match uu____10533 with
                                                     | (t_ps1,t_ty1) ->
                                                         let uu____10548 =
                                                           mapM
                                                             (fun c_lid  ->
                                                                let uu____10576
                                                                  =
                                                                  let uu____10579
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g  in
                                                                  FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu____10579
                                                                    c_lid
                                                                   in
                                                                match uu____10576
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
                                                                    uu____10649
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
                                                                    let uu____10654
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1)
                                                                     in
                                                                    match uu____10654
                                                                    with
                                                                    | 
                                                                    (c_us1,c_ty2)
                                                                    ->
                                                                    let uu____10677
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2  in
                                                                    (match uu____10677
                                                                    with
                                                                    | 
                                                                    (bs,comp)
                                                                    ->
                                                                    let uu____10720
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam bs
                                                                     in
                                                                    (match uu____10720
                                                                    with
                                                                    | 
                                                                    (d_ps,bs1)
                                                                    ->
                                                                    let uu____10793
                                                                    =
                                                                    let uu____10794
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp  in
                                                                    Prims.op_Negation
                                                                    uu____10794
                                                                     in
                                                                    failwhen
                                                                    uu____10793
                                                                    "not total?"
                                                                    (fun
                                                                    uu____10811
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
                                                                    uu___351_10827
                                                                    =
                                                                    match uu___351_10827
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____10830)
                                                                    -> true
                                                                    | 
                                                                    uu____10831
                                                                    -> false
                                                                     in
                                                                    let uu____10834
                                                                    =
                                                                    FStar_List.splitAt
                                                                    nparam
                                                                    args  in
                                                                    match uu____10834
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
                                                                    uu____10967
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
                                                                    uu____11029
                                                                     ->
                                                                    match uu____11029
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11049),
                                                                    (t,uu____11051))
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
                                                                    uu____11119
                                                                     ->
                                                                    match uu____11119
                                                                    with
                                                                    | 
                                                                    ((bv,uu____11145),
                                                                    (t,uu____11147))
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
                                                                    uu____11202
                                                                     ->
                                                                    match uu____11202
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
                                                                    let uu____11252
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    (let uu___414_11269
                                                                    = env  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___414_11269.FStar_TypeChecker_Env.nbe)
                                                                    }) true
                                                                    s_ty pat
                                                                     in
                                                                    match uu____11252
                                                                    with
                                                                    | 
                                                                    (uu____11282,uu____11283,uu____11284,pat_t,uu____11286,uu____11287)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu____11293
                                                                    =
                                                                    let uu____11294
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty
                                                                    s_tm1
                                                                    pat_t  in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    equ
                                                                    uu____11294
                                                                     in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu____11293
                                                                     in
                                                                    let cod1
                                                                    =
                                                                    let uu____11298
                                                                    =
                                                                    let uu____11307
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b  in
                                                                    [uu____11307]
                                                                     in
                                                                    let uu____11326
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod  in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____11298
                                                                    uu____11326
                                                                     in
                                                                    let nty =
                                                                    let uu____11332
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____11332
                                                                     in
                                                                    let uu____11335
                                                                    =
                                                                    new_uvar
                                                                    "destruct branch"
                                                                    env nty
                                                                     in
                                                                    bind
                                                                    uu____11335
                                                                    (fun
                                                                    uu____11364
                                                                     ->
                                                                    match uu____11364
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
                                                                    let uu____11390
                                                                    =
                                                                    let uu____11401
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit
                                                                     in
                                                                    [uu____11401]
                                                                     in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu____11390
                                                                     in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1)  in
                                                                    let uu____11437
                                                                    =
                                                                    let uu____11448
                                                                    =
                                                                    let uu____11453
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_List.length
                                                                    bs2)  in
                                                                    (fv1,
                                                                    uu____11453)
                                                                     in
                                                                    (g', br,
                                                                    uu____11448)
                                                                     in
                                                                    ret
                                                                    uu____11437))))))
                                                                    | 
                                                                    uu____11474
                                                                    ->
                                                                    fail
                                                                    "impossible: not a ctor"))
                                                             c_lids
                                                            in
                                                         bind uu____10548
                                                           (fun goal_brs  ->
                                                              let uu____11523
                                                                =
                                                                FStar_List.unzip3
                                                                  goal_brs
                                                                 in
                                                              match uu____11523
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
                                                                  let uu____11596
                                                                    =
                                                                    solve' g
                                                                    w  in
                                                                  bind
                                                                    uu____11596
                                                                    (
                                                                    fun
                                                                    uu____11607
                                                                     ->
                                                                    let uu____11608
                                                                    =
                                                                    add_goals
                                                                    goals  in
                                                                    bind
                                                                    uu____11608
                                                                    (fun
                                                                    uu____11618
                                                                     ->
                                                                    ret infos))))
                                            | uu____11625 ->
                                                fail "not an inductive type"))))))
       in
    FStar_All.pipe_left (wrap_err "destruct") uu____10283
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____11670::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____11698 = init xs  in x :: uu____11698
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____11710 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      let t3 = FStar_Syntax_Util.unlazy_emb t2  in
      match t3.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t4,uu____11719) -> inspect t4
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____11784 = last args  in
          (match uu____11784 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____11814 =
                 let uu____11815 =
                   let uu____11820 =
                     let uu____11821 =
                       let uu____11826 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____11826  in
                     uu____11821 FStar_Pervasives_Native.None
                       t3.FStar_Syntax_Syntax.pos
                      in
                   (uu____11820, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____11815  in
               FStar_All.pipe_left ret uu____11814)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____11839,uu____11840) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
          let uu____11892 = FStar_Syntax_Subst.open_term bs t4  in
          (match uu____11892 with
           | (bs1,t5) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____11933 =
                      let uu____11934 =
                        let uu____11939 = FStar_Syntax_Util.abs bs2 t5 k  in
                        (b, uu____11939)  in
                      FStar_Reflection_Data.Tv_Abs uu____11934  in
                    FStar_All.pipe_left ret uu____11933))
      | FStar_Syntax_Syntax.Tm_type uu____11942 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____11966 ->
          let uu____11981 = FStar_Syntax_Util.arrow_one t3  in
          (match uu____11981 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t4) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____12011 = FStar_Syntax_Subst.open_term [b] t4  in
          (match uu____12011 with
           | (b',t5) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____12064 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t5)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____12076 =
            let uu____12077 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____12077  in
          FStar_All.pipe_left ret uu____12076
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____12098 =
            let uu____12099 =
              let uu____12104 =
                let uu____12105 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____12105  in
              (uu____12104, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____12099  in
          FStar_All.pipe_left ret uu____12098
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____12139 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____12144 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____12144 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____12197 ->
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
             | FStar_Util.Inr uu____12231 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____12235 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____12235 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12255 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____12259 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t4,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____12313 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____12313
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____12332 =
                  let uu____12339 =
                    FStar_List.map
                      (fun uu____12351  ->
                         match uu____12351 with
                         | (p1,uu____12359) -> inspect_pat p1) ps
                     in
                  (fv, uu____12339)  in
                FStar_Reflection_Data.Pat_Cons uu____12332
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
              (fun uu___352_12453  ->
                 match uu___352_12453 with
                 | (pat,uu____12475,t5) ->
                     let uu____12493 = inspect_pat pat  in (uu____12493, t5))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t4, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____12502 ->
          ((let uu____12504 =
              let uu____12509 =
                let uu____12510 = FStar_Syntax_Print.tag_of_term t3  in
                let uu____12511 = FStar_Syntax_Print.term_to_string t3  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____12510 uu____12511
                 in
              (FStar_Errors.Warning_CantInspect, uu____12509)  in
            FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____12504);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____11710
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____12524 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____12524
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____12528 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____12528
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____12532 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____12532
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____12539 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____12539
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____12564 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____12564
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____12581 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____12581
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____12600 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____12600
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____12604 =
          let uu____12605 =
            let uu____12612 =
              let uu____12613 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____12613  in
            FStar_Syntax_Syntax.mk uu____12612  in
          uu____12605 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12604
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____12621 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12621
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12630 =
          let uu____12631 =
            let uu____12638 =
              let uu____12639 =
                let uu____12652 =
                  let uu____12655 =
                    let uu____12656 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____12656]  in
                  FStar_Syntax_Subst.close uu____12655 t2  in
                ((false, [lb]), uu____12652)  in
              FStar_Syntax_Syntax.Tm_let uu____12639  in
            FStar_Syntax_Syntax.mk uu____12638  in
          uu____12631 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____12630
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____12696 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____12696 with
         | (lbs,body) ->
             let uu____12711 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____12711)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____12745 =
                let uu____12746 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____12746  in
              FStar_All.pipe_left wrap uu____12745
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____12753 =
                let uu____12754 =
                  let uu____12767 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____12783 = pack_pat p1  in
                         (uu____12783, false)) ps
                     in
                  (fv, uu____12767)  in
                FStar_Syntax_Syntax.Pat_cons uu____12754  in
              FStar_All.pipe_left wrap uu____12753
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
            (fun uu___353_12829  ->
               match uu___353_12829 with
               | (pat,t1) ->
                   let uu____12846 = pack_pat pat  in
                   (uu____12846, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____12894 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12894
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____12922 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12922
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____12968 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____12968
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____13007 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____13007
  
let (lget :
  FStar_Reflection_Data.typ -> Prims.string -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun k  ->
      let uu____13024 =
        bind get
          (fun ps  ->
             let uu____13030 =
               FStar_Util.psmap_try_find ps.FStar_Tactics_Types.local_state k
                in
             match uu____13030 with
             | FStar_Pervasives_Native.None  -> fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t)
         in
      FStar_All.pipe_left (wrap_err "lget") uu____13024
  
let (lset :
  FStar_Reflection_Data.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit tac)
  =
  fun _ty  ->
    fun k  ->
      fun t  ->
        let uu____13059 =
          bind get
            (fun ps  ->
               let ps1 =
                 let uu___415_13066 = ps  in
                 let uu____13067 =
                   FStar_Util.psmap_add ps.FStar_Tactics_Types.local_state k
                     t
                    in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___415_13066.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___415_13066.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___415_13066.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___415_13066.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___415_13066.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___415_13066.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___415_13066.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___415_13066.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___415_13066.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___415_13066.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (uu___415_13066.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___415_13066.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu____13067
                 }  in
               set ps1)
           in
        FStar_All.pipe_left (wrap_err "lset") uu____13059
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____13092 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____13092 with
      | (u,ctx_uvars,g_u) ->
          let uu____13124 = FStar_List.hd ctx_uvars  in
          (match uu____13124 with
           | (ctx_uvar,uu____13138) ->
               let g =
                 let uu____13140 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____13140 false
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
        let uu____13160 = goal_of_goal_ty env typ  in
        match uu____13160 with
        | (g,g_u) ->
            let ps =
              let uu____13172 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "TacVerbose")
                 in
              let uu____13173 = FStar_Util.psmap_empty ()  in
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
                FStar_Tactics_Types.tac_verb_dbg = uu____13172;
                FStar_Tactics_Types.local_state = uu____13173
              }  in
            let uu____13180 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____13180)
  