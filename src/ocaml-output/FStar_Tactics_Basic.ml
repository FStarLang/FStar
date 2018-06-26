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
      | e ->
          let uu____164 =
            let uu____169 = FStar_Util.message_of_exn e  in (uu____169, p)
             in
          FStar_Tactics_Result.Failed uu____164
  
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
           let uu____241 = run t1 p  in
           match uu____241 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____248 = t2 a  in run uu____248 q
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
    let uu____268 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____268 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string_verbose : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____286 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____287 =
      let uu____288 = check_goal_solved g  in
      match uu____288 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____292 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____292
       in
    FStar_Util.format2 "%s%s" uu____286 uu____287
  
let (goal_to_string :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> Prims.string)
  =
  fun ps  ->
    fun g  ->
      let uu____303 =
        (FStar_Options.print_implicits ()) ||
          ps.FStar_Tactics_Types.tac_verb_dbg
         in
      if uu____303
      then goal_to_string_verbose g
      else
        (let w =
           let uu____306 =
             get_uvar_solved g.FStar_Tactics_Types.goal_ctx_uvar  in
           match uu____306 with
           | FStar_Pervasives_Native.None  -> "_"
           | FStar_Pervasives_Native.Some t ->
               let uu____310 = FStar_Tactics_Types.goal_env g  in
               tts uu____310 t
            in
         let uu____311 =
           FStar_Syntax_Print.binders_to_string ", "
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            in
         let uu____312 =
           let uu____313 = FStar_Tactics_Types.goal_env g  in
           tts uu____313
             (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
            in
         FStar_Util.format3 "%s |- %s : %s" uu____311 w uu____312)
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____329 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____329
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____345 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____345
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____366 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____366
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____373) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____383) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____398 =
      let uu____403 =
        let uu____404 = FStar_Tactics_Types.goal_env g  in
        let uu____405 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____404 uu____405  in
      FStar_Syntax_Util.un_squash uu____403  in
    match uu____398 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____411 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____439 =
            let uu____440 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____440  in
          if uu____439 then tacprint msg else ());
         ret ())
  
let (dump_goal :
  FStar_Tactics_Types.proofstate -> FStar_Tactics_Types.goal -> unit) =
  fun ps  ->
    fun goal  ->
      let uu____453 = goal_to_string ps goal  in tacprint uu____453
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____465 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____469 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____469))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____478  ->
    match uu____478 with
    | (msg,ps) ->
        let uu____485 =
          let uu____488 =
            let uu____489 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____489 msg
             in
          let uu____490 =
            let uu____493 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____494 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____494
              else ""  in
            let uu____496 =
              let uu____499 =
                let uu____500 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____501 =
                  let uu____502 =
                    FStar_List.map (goal_to_string ps)
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____502  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____500
                  uu____501
                 in
              let uu____505 =
                let uu____508 =
                  let uu____509 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____510 =
                    let uu____511 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____511  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____509
                    uu____510
                   in
                [uu____508]  in
              uu____499 :: uu____505  in
            uu____493 :: uu____496  in
          uu____488 :: uu____490  in
        FStar_String.concat "" uu____485
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____520 =
        let uu____521 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____521  in
      let uu____522 =
        let uu____527 =
          let uu____528 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____528  in
        FStar_Syntax_Print.binders_to_json uu____527  in
      FStar_All.pipe_right uu____520 uu____522  in
    let uu____529 =
      let uu____536 =
        let uu____543 =
          let uu____548 =
            let uu____549 =
              let uu____556 =
                let uu____561 =
                  let uu____562 =
                    let uu____563 = FStar_Tactics_Types.goal_env g  in
                    let uu____564 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____563 uu____564  in
                  FStar_Util.JsonStr uu____562  in
                ("witness", uu____561)  in
              let uu____565 =
                let uu____572 =
                  let uu____577 =
                    let uu____578 =
                      let uu____579 = FStar_Tactics_Types.goal_env g  in
                      let uu____580 = FStar_Tactics_Types.goal_type g  in
                      tts uu____579 uu____580  in
                    FStar_Util.JsonStr uu____578  in
                  ("type", uu____577)  in
                [uu____572]  in
              uu____556 :: uu____565  in
            FStar_Util.JsonAssoc uu____549  in
          ("goal", uu____548)  in
        [uu____543]  in
      ("hyps", g_binders) :: uu____536  in
    FStar_Util.JsonAssoc uu____529
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____613  ->
    match uu____613 with
    | (msg,ps) ->
        let uu____620 =
          let uu____627 =
            let uu____634 =
              let uu____641 =
                let uu____648 =
                  let uu____653 =
                    let uu____654 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____654  in
                  ("goals", uu____653)  in
                let uu____657 =
                  let uu____664 =
                    let uu____669 =
                      let uu____670 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____670  in
                    ("smt-goals", uu____669)  in
                  [uu____664]  in
                uu____648 :: uu____657  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____641
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____634  in
          let uu____693 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____706 =
                let uu____711 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____711)  in
              [uu____706]
            else []  in
          FStar_List.append uu____627 uu____693  in
        FStar_Util.JsonAssoc uu____620
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____741  ->
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
         (let uu____764 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____764 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____782 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____782 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____836 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____836
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____844 . Prims.string -> Prims.string -> 'Auu____844 tac =
  fun msg  ->
    fun x  -> let uu____857 = FStar_Util.format1 msg x  in fail uu____857
  
let fail2 :
  'Auu____866 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____866 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____884 = FStar_Util.format2 msg x y  in fail uu____884
  
let fail3 :
  'Auu____895 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____895 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____918 = FStar_Util.format3 msg x y z  in fail uu____918
  
let fail4 :
  'Auu____931 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____931 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____959 = FStar_Util.format4 msg x y z w  in fail uu____959
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____992 = run t ps  in
         match uu____992 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___348_1016 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___348_1016.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___348_1016.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___348_1016.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___348_1016.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___348_1016.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___348_1016.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___348_1016.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___348_1016.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___348_1016.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___348_1016.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___348_1016.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1043 = trytac' t  in
    bind uu____1043
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1070 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1106 = trytac t  in run uu____1106 ps
         with
         | FStar_Errors.Err (uu____1122,msg) ->
             (log ps
                (fun uu____1126  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1131,msg,uu____1133) ->
             (log ps
                (fun uu____1136  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1169 = run t ps  in
           match uu____1169 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1188  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1209 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1209
         then
           let uu____1210 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1211 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1210
             uu____1211
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1223 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1223
            then
              let uu____1224 = FStar_Util.string_of_bool res  in
              let uu____1225 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1226 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1224 uu____1225 uu____1226
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1234,msg) ->
             mlog
               (fun uu____1237  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1239  -> ret false)
         | FStar_Errors.Error (uu____1240,msg,r) ->
             mlog
               (fun uu____1245  ->
                  let uu____1246 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1246) (fun uu____1248  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1271  ->
             (let uu____1273 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1273
              then
                (FStar_Options.push ();
                 (let uu____1275 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1277 =
                let uu____1280 = __do_unify env t1 t2  in
                bind uu____1280
                  (fun b  ->
                     if Prims.op_Negation b
                     then
                       let t11 =
                         FStar_TypeChecker_Normalize.normalize [] env t1  in
                       let t21 =
                         FStar_TypeChecker_Normalize.normalize [] env t2  in
                       __do_unify env t11 t21
                     else ret b)
                 in
              bind uu____1277
                (fun r  ->
                   (let uu____1296 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1296 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___353_1304 = ps  in
         let uu____1305 =
           FStar_List.filter
             (fun g  ->
                let uu____1311 = check_goal_solved g  in
                FStar_Option.isNone uu____1311) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___353_1304.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___353_1304.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___353_1304.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1305;
           FStar_Tactics_Types.smt_goals =
             (uu___353_1304.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___353_1304.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___353_1304.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___353_1304.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___353_1304.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___353_1304.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___353_1304.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___353_1304.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1328 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1328 with
      | FStar_Pervasives_Native.Some uu____1333 ->
          let uu____1334 =
            let uu____1335 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1335  in
          fail uu____1334
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1351 = FStar_Tactics_Types.goal_env goal  in
      let uu____1352 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1351 solution uu____1352
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1358 =
         let uu___354_1359 = p  in
         let uu____1360 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_1359.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___354_1359.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___354_1359.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1360;
           FStar_Tactics_Types.smt_goals =
             (uu___354_1359.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_1359.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_1359.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_1359.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_1359.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_1359.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_1359.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_1359.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1358)
  
let (dismiss : unit -> unit tac) =
  fun uu____1369  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1376 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1397  ->
           let uu____1398 =
             let uu____1399 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1399  in
           let uu____1400 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1398 uu____1400)
        (fun uu____1403  ->
           let uu____1404 = trysolve goal solution  in
           bind uu____1404
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1412  -> remove_solved_goals)
                else
                  (let uu____1414 =
                     let uu____1415 =
                       let uu____1416 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1416 solution  in
                     let uu____1417 =
                       let uu____1418 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1419 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1418 uu____1419  in
                     let uu____1420 =
                       let uu____1421 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1422 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1421 uu____1422  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1415 uu____1417 uu____1420
                      in
                   fail uu____1414)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1437 = set_solution goal solution  in
      bind uu____1437
        (fun uu____1441  ->
           bind __dismiss (fun uu____1443  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___355_1450 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___355_1450.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___355_1450.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___355_1450.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___355_1450.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___355_1450.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___355_1450.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___355_1450.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___355_1450.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___355_1450.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___355_1450.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___355_1450.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1469 = FStar_Options.defensive ()  in
    if uu____1469
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1474 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1474)
         in
      let b2 =
        b1 &&
          (let uu____1477 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1477)
         in
      let rec aux b3 e =
        let uu____1489 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1489 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1507 =
        (let uu____1510 = aux b2 env  in Prims.op_Negation uu____1510) &&
          (let uu____1512 = FStar_ST.op_Bang nwarn  in
           uu____1512 < (Prims.parse_int "5"))
         in
      (if uu____1507
       then
         ((let uu____1537 =
             let uu____1538 = FStar_Tactics_Types.goal_type g  in
             uu____1538.FStar_Syntax_Syntax.pos  in
           let uu____1541 =
             let uu____1546 =
               let uu____1547 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1547
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1546)  in
           FStar_Errors.log_issue uu____1537 uu____1541);
          (let uu____1548 =
             let uu____1549 = FStar_ST.op_Bang nwarn  in
             uu____1549 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1548))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___356_1617 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___356_1617.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___356_1617.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___356_1617.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___356_1617.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___356_1617.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___356_1617.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___356_1617.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___356_1617.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___356_1617.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___356_1617.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___356_1617.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1637 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1637.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1637.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1637.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___357_1637.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_1637.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1637.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1637.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1637.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1637.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1637.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1637.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_1657 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1657.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1657.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_1657.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___358_1657.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_1657.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1657.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1657.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1657.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1657.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1657.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1657.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___359_1677 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1677.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1677.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_1677.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___359_1677.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___359_1677.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1677.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1677.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1677.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1677.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1677.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1677.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1688  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___360_1702 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1702.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1702.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1702.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___360_1702.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___360_1702.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1702.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1702.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1702.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1702.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1702.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1702.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1738 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1738 with
        | (u,ctx_uvar,g_u) ->
            let uu____1772 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1772
              (fun uu____1781  ->
                 let uu____1782 =
                   let uu____1787 =
                     let uu____1788 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1788  in
                   (u, uu____1787)  in
                 ret uu____1782)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1806 = FStar_Syntax_Util.un_squash t  in
    match uu____1806 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1816 =
          let uu____1817 = FStar_Syntax_Subst.compress t'  in
          uu____1817.FStar_Syntax_Syntax.n  in
        (match uu____1816 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1821 -> false)
    | uu____1822 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1832 = FStar_Syntax_Util.un_squash t  in
    match uu____1832 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1842 =
          let uu____1843 = FStar_Syntax_Subst.compress t'  in
          uu____1843.FStar_Syntax_Syntax.n  in
        (match uu____1842 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1847 -> false)
    | uu____1848 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1859  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1870 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1870 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1877 = goal_to_string_verbose hd1  in
                    let uu____1878 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1877 uu____1878);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1885  ->
    let uu____1888 =
      bind get
        (fun ps  ->
           let uu____1894 = cur_goal ()  in
           bind uu____1894
             (fun g  ->
                (let uu____1901 =
                   let uu____1902 = FStar_Tactics_Types.goal_type g  in
                   uu____1902.FStar_Syntax_Syntax.pos  in
                 let uu____1905 =
                   let uu____1910 =
                     let uu____1911 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1911
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1910)  in
                 FStar_Errors.log_issue uu____1901 uu____1905);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1888
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1922  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___361_1932 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___361_1932.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___361_1932.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___361_1932.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___361_1932.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___361_1932.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___361_1932.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___361_1932.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___361_1932.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___361_1932.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___361_1932.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___361_1932.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1933 = set ps1  in
         bind uu____1933
           (fun uu____1938  ->
              let uu____1939 = FStar_BigInt.of_int_fs n1  in ret uu____1939))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1946  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1954 = FStar_BigInt.of_int_fs n1  in ret uu____1954)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1967  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1975 = FStar_BigInt.of_int_fs n1  in ret uu____1975)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1988  ->
    let uu____1991 = cur_goal ()  in
    bind uu____1991 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2023 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2023 phi  in
          let uu____2024 = new_uvar reason env typ  in
          bind uu____2024
            (fun uu____2039  ->
               match uu____2039 with
               | (uu____2046,ctx_uvar) ->
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
             (fun uu____2091  ->
                let uu____2092 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2092)
             (fun uu____2095  ->
                let e1 =
                  let uu___362_2097 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___362_2097.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___362_2097.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___362_2097.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___362_2097.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___362_2097.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___362_2097.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___362_2097.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___362_2097.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___362_2097.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___362_2097.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___362_2097.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___362_2097.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___362_2097.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___362_2097.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___362_2097.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___362_2097.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___362_2097.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___362_2097.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___362_2097.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___362_2097.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___362_2097.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.failhard =
                      (uu___362_2097.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___362_2097.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___362_2097.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___362_2097.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___362_2097.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___362_2097.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___362_2097.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___362_2097.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___362_2097.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___362_2097.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___362_2097.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___362_2097.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___362_2097.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___362_2097.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___362_2097.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___362_2097.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___362_2097.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___362_2097.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  let uu____2117 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2117
                with
                | FStar_Errors.Err (uu____2144,msg) ->
                    let uu____2146 = tts e1 t  in
                    let uu____2147 =
                      let uu____2148 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2148
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2146 uu____2147 msg
                | FStar_Errors.Error (uu____2155,msg,uu____2157) ->
                    let uu____2158 = tts e1 t  in
                    let uu____2159 =
                      let uu____2160 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2160
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2158 uu____2159 msg))
  
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
  fun uu____2187  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___365_2205 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___365_2205.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___365_2205.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___365_2205.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___365_2205.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___365_2205.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___365_2205.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___365_2205.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___365_2205.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___365_2205.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___365_2205.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___365_2205.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2229 = get_guard_policy ()  in
      bind uu____2229
        (fun old_pol  ->
           let uu____2235 = set_guard_policy pol  in
           bind uu____2235
             (fun uu____2239  ->
                bind t
                  (fun r  ->
                     let uu____2243 = set_guard_policy old_pol  in
                     bind uu____2243 (fun uu____2247  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2250 = let uu____2255 = cur_goal ()  in trytac uu____2255  in
  bind uu____2250
    (fun uu___338_2262  ->
       match uu___338_2262 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2268 = FStar_Options.peek ()  in ret uu____2268)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2291 =
               let uu____2292 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2292.FStar_TypeChecker_Env.guard_f  in
             match uu____2291 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2296 = istrivial e f  in
                 if uu____2296
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2304 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2304
                              (fun goal  ->
                                 let goal1 =
                                   let uu___366_2311 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___366_2311.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___366_2311.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___366_2311.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2312 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2312
                              (fun goal  ->
                                 let goal1 =
                                   let uu___367_2319 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___367_2319.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___367_2319.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___367_2319.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2327 =
                                 let uu____2328 =
                                   let uu____2329 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2329
                                    in
                                 Prims.op_Negation uu____2328  in
                               if uu____2327
                               then
                                 mlog
                                   (fun uu____2334  ->
                                      let uu____2335 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2335)
                                   (fun uu____2337  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2344 ->
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
             (fun uu____2390  ->
                match uu____2390 with
                | (t1,typ,guard) ->
                    let uu____2402 =
                      let uu____2405 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2405 guard  in
                    bind uu____2402 (fun uu____2407  -> ret typ)))
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
          let uu____2436 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2436 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2447  ->
    let uu____2450 = cur_goal ()  in
    bind uu____2450
      (fun goal  ->
         let uu____2456 =
           let uu____2457 = FStar_Tactics_Types.goal_env goal  in
           let uu____2458 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2457 uu____2458  in
         if uu____2456
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2462 =
              let uu____2463 = FStar_Tactics_Types.goal_env goal  in
              let uu____2464 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2463 uu____2464  in
            fail1 "Not a trivial goal: %s" uu____2462))
  
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
          let uu____2493 =
            let uu____2494 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2494.FStar_TypeChecker_Env.guard_f  in
          match uu____2493 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2502 = istrivial e f  in
              if uu____2502
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2510 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2510
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___370_2520 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___370_2520.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___370_2520.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___370_2520.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2527  ->
    let uu____2530 = cur_goal ()  in
    bind uu____2530
      (fun g  ->
         let uu____2536 = is_irrelevant g  in
         if uu____2536
         then bind __dismiss (fun uu____2540  -> add_smt_goals [g])
         else
           (let uu____2542 =
              let uu____2543 = FStar_Tactics_Types.goal_env g  in
              let uu____2544 = FStar_Tactics_Types.goal_type g  in
              tts uu____2543 uu____2544  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2542))
  
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
             let uu____2593 =
               try
                 let uu____2627 =
                   let uu____2636 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2636 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2627
               with | uu____2658 -> fail "divide: not enough goals"  in
             bind uu____2593
               (fun uu____2685  ->
                  match uu____2685 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___371_2711 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___371_2711.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___371_2711.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___371_2711.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___371_2711.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___371_2711.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___371_2711.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___371_2711.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___371_2711.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___371_2711.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___371_2711.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let rp =
                        let uu___372_2713 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___372_2713.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___372_2713.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___372_2713.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___372_2713.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___372_2713.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___372_2713.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___372_2713.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___372_2713.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___372_2713.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___372_2713.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2714 = set lp  in
                      bind uu____2714
                        (fun uu____2722  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2736 = set rp  in
                                     bind uu____2736
                                       (fun uu____2744  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___373_2760 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___373_2760.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___373_2760.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2761 = set p'
                                                       in
                                                    bind uu____2761
                                                      (fun uu____2769  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2775 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2796 = divide FStar_BigInt.one f idtac  in
    bind uu____2796
      (fun uu____2809  -> match uu____2809 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2846::uu____2847 ->
             let uu____2850 =
               let uu____2859 = map tau  in
               divide FStar_BigInt.one tau uu____2859  in
             bind uu____2850
               (fun uu____2877  ->
                  match uu____2877 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2918 =
        bind t1
          (fun uu____2923  ->
             let uu____2924 = map t2  in
             bind uu____2924 (fun uu____2932  -> ret ()))
         in
      focus uu____2918
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2941  ->
    let uu____2944 =
      let uu____2947 = cur_goal ()  in
      bind uu____2947
        (fun goal  ->
           let uu____2956 =
             let uu____2963 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2963  in
           match uu____2956 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2972 =
                 let uu____2973 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2973  in
               if uu____2972
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2978 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2978 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2988 = new_uvar "intro" env' typ'  in
                  bind uu____2988
                    (fun uu____3004  ->
                       match uu____3004 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3024 = set_solution goal sol  in
                           bind uu____3024
                             (fun uu____3030  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3032 =
                                  let uu____3035 = bnorm_goal g  in
                                  replace_cur uu____3035  in
                                bind uu____3032 (fun uu____3037  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3042 =
                 let uu____3043 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3044 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3043 uu____3044  in
               fail1 "goal is not an arrow (%s)" uu____3042)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2944
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3059  ->
    let uu____3066 = cur_goal ()  in
    bind uu____3066
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3083 =
            let uu____3090 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3090  in
          match uu____3083 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3103 =
                let uu____3104 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3104  in
              if uu____3103
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3117 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3117
                    in
                 let bs =
                   let uu____3125 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3125; b]  in
                 let env' =
                   let uu____3143 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3143 bs  in
                 let uu____3144 =
                   let uu____3151 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3151  in
                 bind uu____3144
                   (fun uu____3170  ->
                      match uu____3170 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3184 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3187 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3184
                              FStar_Parser_Const.effect_Tot_lid uu____3187 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3201 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3201 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3223 =
                                   let uu____3224 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3224.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3223
                                  in
                               let uu____3237 = set_solution goal tm  in
                               bind uu____3237
                                 (fun uu____3246  ->
                                    let uu____3247 =
                                      let uu____3250 =
                                        bnorm_goal
                                          (let uu___376_3253 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___376_3253.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___376_3253.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___376_3253.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3250  in
                                    bind uu____3247
                                      (fun uu____3260  ->
                                         let uu____3261 =
                                           let uu____3266 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3266, b)  in
                                         ret uu____3261)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3275 =
                let uu____3276 = FStar_Tactics_Types.goal_env goal  in
                let uu____3277 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3276 uu____3277  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3275))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3295 = cur_goal ()  in
    bind uu____3295
      (fun goal  ->
         mlog
           (fun uu____3302  ->
              let uu____3303 =
                let uu____3304 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3304  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3303)
           (fun uu____3309  ->
              let steps =
                let uu____3313 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3313
                 in
              let t =
                let uu____3317 = FStar_Tactics_Types.goal_env goal  in
                let uu____3318 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3317 uu____3318  in
              let uu____3319 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3319))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3343 =
          mlog
            (fun uu____3348  ->
               let uu____3349 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3349)
            (fun uu____3351  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3357 -> g.FStar_Tactics_Types.opts
                      | uu____3360 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3365  ->
                         let uu____3366 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3366)
                      (fun uu____3369  ->
                         let uu____3370 = __tc e t  in
                         bind uu____3370
                           (fun uu____3391  ->
                              match uu____3391 with
                              | (t1,uu____3401,uu____3402) ->
                                  let steps =
                                    let uu____3406 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3406
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3343
  
let (refine_intro : unit -> unit tac) =
  fun uu____3420  ->
    let uu____3423 =
      let uu____3426 = cur_goal ()  in
      bind uu____3426
        (fun g  ->
           let uu____3433 =
             let uu____3444 = FStar_Tactics_Types.goal_env g  in
             let uu____3445 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3444 uu____3445
              in
           match uu____3433 with
           | (uu____3448,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3473 =
                 let uu____3478 =
                   let uu____3483 =
                     let uu____3484 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3484]  in
                   FStar_Syntax_Subst.open_term uu____3483 phi  in
                 match uu____3478 with
                 | (bvs,phi1) ->
                     let uu____3503 =
                       let uu____3504 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3504  in
                     (uu____3503, phi1)
                  in
               (match uu____3473 with
                | (bv1,phi1) ->
                    let uu____3517 =
                      let uu____3520 = FStar_Tactics_Types.goal_env g  in
                      let uu____3521 =
                        let uu____3522 =
                          let uu____3525 =
                            let uu____3526 =
                              let uu____3533 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3533)  in
                            FStar_Syntax_Syntax.NT uu____3526  in
                          [uu____3525]  in
                        FStar_Syntax_Subst.subst uu____3522 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3520
                        uu____3521 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3517
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3541  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3423
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3560 = cur_goal ()  in
      bind uu____3560
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3568 = FStar_Tactics_Types.goal_env goal  in
               let uu____3569 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3568 uu____3569
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3571 = __tc env t  in
           bind uu____3571
             (fun uu____3590  ->
                match uu____3590 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3605  ->
                         let uu____3606 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3607 =
                           let uu____3608 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3608
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3606 uu____3607)
                      (fun uu____3611  ->
                         let uu____3612 =
                           let uu____3615 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3615 guard  in
                         bind uu____3612
                           (fun uu____3617  ->
                              mlog
                                (fun uu____3621  ->
                                   let uu____3622 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3623 =
                                     let uu____3624 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3624
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3622 uu____3623)
                                (fun uu____3627  ->
                                   let uu____3628 =
                                     let uu____3631 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3632 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3631 typ uu____3632  in
                                   bind uu____3628
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3638 =
                                             let uu____3639 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3639 t1  in
                                           let uu____3640 =
                                             let uu____3641 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3641 typ  in
                                           let uu____3642 =
                                             let uu____3643 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3644 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3643 uu____3644  in
                                           let uu____3645 =
                                             let uu____3646 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3647 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3646 uu____3647  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3638 uu____3640 uu____3642
                                             uu____3645)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3662 =
        mlog
          (fun uu____3667  ->
             let uu____3668 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3668)
          (fun uu____3671  ->
             let uu____3672 =
               let uu____3679 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3679  in
             bind uu____3672
               (fun uu___340_3688  ->
                  match uu___340_3688 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3698  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3701  ->
                           let uu____3702 =
                             let uu____3709 =
                               let uu____3712 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3712
                                 (fun uu____3717  ->
                                    let uu____3718 = refine_intro ()  in
                                    bind uu____3718
                                      (fun uu____3722  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3709  in
                           bind uu____3702
                             (fun uu___339_3729  ->
                                match uu___339_3729 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3737 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3662
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3766 =
             let uu____3769 =
               let uu____3772 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3772  in
             FStar_Util.set_elements uu____3769  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3766
            in
         FStar_List.existsML (FStar_Syntax_Unionfind.equiv u) free_uvars)
  
let (uvar_free :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.proofstate -> Prims.bool) =
  fun u  ->
    fun ps  ->
      FStar_List.existsML (uvar_free_in_goal u) ps.FStar_Tactics_Types.goals
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3850 = f x  in
          bind uu____3850
            (fun y  ->
               let uu____3858 = mapM f xs  in
               bind uu____3858 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3878 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3898 = cur_goal ()  in
        bind uu____3898
          (fun goal  ->
             mlog
               (fun uu____3905  ->
                  let uu____3906 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3906)
               (fun uu____3909  ->
                  let uu____3910 =
                    let uu____3915 =
                      let uu____3918 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3918  in
                    trytac_exn uu____3915  in
                  bind uu____3910
                    (fun uu___341_3925  ->
                       match uu___341_3925 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3933  ->
                                let uu____3934 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3934)
                             (fun uu____3937  ->
                                let uu____3938 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3938 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3962  ->
                                         let uu____3963 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3963)
                                      (fun uu____3966  ->
                                         let uu____3967 =
                                           let uu____3968 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3968  in
                                         if uu____3967
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3972 =
                                              let uu____3979 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____3979
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3972
                                              (fun uu____3990  ->
                                                 match uu____3990 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____4017 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____4017
                                                        in
                                                     let uu____4020 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____4020
                                                       (fun uu____4028  ->
                                                          let u1 =
                                                            let uu____4030 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4030
                                                              u
                                                             in
                                                          let uu____4031 =
                                                            let uu____4032 =
                                                              let uu____4035
                                                                =
                                                                let uu____4036
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4036
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4035
                                                               in
                                                            uu____4032.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4031
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4064)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4084
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4084
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    (let uu____4088
                                                                    =
                                                                    let uu____4091
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___377_4094
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___377_4094.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___377_4094.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })  in
                                                                    [uu____4091]
                                                                     in
                                                                    add_goals
                                                                    uu____4088))
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4149 =
        mlog
          (fun uu____4154  ->
             let uu____4155 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4155)
          (fun uu____4158  ->
             let uu____4159 = cur_goal ()  in
             bind uu____4159
               (fun goal  ->
                  let uu____4165 =
                    let uu____4174 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4174 tm  in
                  bind uu____4165
                    (fun uu____4188  ->
                       match uu____4188 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4201 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4201 typ  in
                           let uu____4202 =
                             let uu____4205 =
                               let uu____4208 = __apply uopt tm1 typ1  in
                               bind uu____4208
                                 (fun uu____4213  ->
                                    let uu____4214 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4214 guard)
                                in
                             focus uu____4205  in
                           let uu____4215 =
                             let uu____4218 =
                               let uu____4219 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4219 tm1  in
                             let uu____4220 =
                               let uu____4221 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4221 typ1  in
                             let uu____4222 =
                               let uu____4223 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4224 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4223 uu____4224  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4218 uu____4220 uu____4222
                              in
                           try_unif uu____4202 uu____4215)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4149
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4247 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4247
    then
      let uu____4254 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4269 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4308 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4254 with
      | (pre,post) ->
          let post1 =
            let uu____4338 =
              let uu____4347 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4347]  in
            FStar_Syntax_Util.mk_app post uu____4338  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4371 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4371
       then
         let uu____4378 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4378
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4411 =
      let uu____4414 =
        mlog
          (fun uu____4419  ->
             let uu____4420 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4420)
          (fun uu____4424  ->
             let is_unit_t t =
               let uu____4431 =
                 let uu____4432 = FStar_Syntax_Subst.compress t  in
                 uu____4432.FStar_Syntax_Syntax.n  in
               match uu____4431 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4436 -> false  in
             let uu____4437 = cur_goal ()  in
             bind uu____4437
               (fun goal  ->
                  let uu____4443 =
                    let uu____4452 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4452 tm  in
                  bind uu____4443
                    (fun uu____4467  ->
                       match uu____4467 with
                       | (tm1,t,guard) ->
                           let uu____4479 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4479 with
                            | (bs,comp) ->
                                let uu____4506 = lemma_or_sq comp  in
                                (match uu____4506 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4525 =
                                       FStar_List.fold_left
                                         (fun uu____4567  ->
                                            fun uu____4568  ->
                                              match (uu____4567, uu____4568)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4659 =
                                                    is_unit_t b_t  in
                                                  if uu____4659
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4689 =
                                                       let uu____4702 =
                                                         let uu____4703 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4703.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4706 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4702
                                                         uu____4706 b_t
                                                        in
                                                     match uu____4689 with
                                                     | (u,uu____4722,g_u) ->
                                                         let uu____4736 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4736,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4525 with
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
                                          let uu____4797 =
                                            let uu____4800 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4801 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4802 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4800 uu____4801
                                              uu____4802
                                             in
                                          bind uu____4797
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4810 =
                                                   let uu____4811 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4811 tm1  in
                                                 let uu____4812 =
                                                   let uu____4813 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4814 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4813 uu____4814
                                                    in
                                                 let uu____4815 =
                                                   let uu____4816 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4817 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4816 uu____4817
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4810 uu____4812
                                                   uu____4815
                                               else
                                                 (let uu____4819 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4819
                                                    (fun uu____4824  ->
                                                       let uu____4825 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4825
                                                         (fun uu____4833  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4858
                                                                  =
                                                                  let uu____4861
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4861
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4858
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
                                                                   let uu____4896
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4896)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4912
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4912
                                                              with
                                                              | (hd1,uu____4928)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4950)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____4967
                                                                    -> false)
                                                               in
                                                            let uu____4968 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5031
                                                                     ->
                                                                    match uu____5031
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range)
                                                                    ->
                                                                    let uu____5054
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5054
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5080)
                                                                    ->
                                                                    let uu____5101
                                                                    =
                                                                    let uu____5102
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5102.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5101
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5116)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___380_5136
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___380_5136.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___380_5136.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___380_5136.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5149
                                                                    ->
                                                                    let env =
                                                                    let uu___381_5151
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___381_5151.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5153
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5153
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
                                                                    let uu____5156
                                                                    =
                                                                    let uu____5163
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5163
                                                                    term1  in
                                                                    match uu____5156
                                                                    with
                                                                    | 
                                                                    (uu____5164,uu____5165,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5167
                                                                    =
                                                                    let uu____5172
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5172
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5167
                                                                    (fun
                                                                    uu___342_5184
                                                                     ->
                                                                    match uu___342_5184
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
                                                                    ([], [g]))))))
                                                               in
                                                            bind uu____4968
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5252
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5252
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5274
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5274
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5335
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5335
                                                                    then
                                                                    let uu____5338
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5338
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
                                                                    let uu____5352
                                                                    =
                                                                    let uu____5353
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5353
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5352)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5354
                                                                   =
                                                                   let uu____5357
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5357
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5354
                                                                   (fun
                                                                    uu____5360
                                                                     ->
                                                                    let uu____5361
                                                                    =
                                                                    let uu____5364
                                                                    =
                                                                    let uu____5365
                                                                    =
                                                                    let uu____5366
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5367
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5366
                                                                    uu____5367
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5365
                                                                     in
                                                                    if
                                                                    uu____5364
                                                                    then
                                                                    let uu____5370
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5370
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5361
                                                                    (fun
                                                                    uu____5374
                                                                     ->
                                                                    let uu____5375
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5375
                                                                    (fun
                                                                    uu____5379
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4414  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4411
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5401 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5401 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5411::(e1,uu____5413)::(e2,uu____5415)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5458 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5482 = destruct_eq' typ  in
    match uu____5482 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5512 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5512 with
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
        let uu____5574 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5574 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5622 = aux e'  in
               FStar_Util.map_opt uu____5622
                 (fun uu____5646  ->
                    match uu____5646 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5667 = aux e  in
      FStar_Util.map_opt uu____5667
        (fun uu____5691  ->
           match uu____5691 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5758 =
            let uu____5767 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5767  in
          FStar_Util.map_opt uu____5758
            (fun uu____5782  ->
               match uu____5782 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___382_5801 = bv  in
                     let uu____5802 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___382_5801.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___382_5801.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5802
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___383_5810 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5811 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5818 =
                       let uu____5821 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5821  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___383_5810.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5811;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5818;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___383_5810.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___383_5810.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___383_5810.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___384_5822 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___384_5822.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___384_5822.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___384_5822.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5832 =
      let uu____5835 = cur_goal ()  in
      bind uu____5835
        (fun goal  ->
           let uu____5843 = h  in
           match uu____5843 with
           | (bv,uu____5847) ->
               mlog
                 (fun uu____5851  ->
                    let uu____5852 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5853 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5852
                      uu____5853)
                 (fun uu____5856  ->
                    let uu____5857 =
                      let uu____5866 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5866  in
                    match uu____5857 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5887 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5887 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5902 =
                               let uu____5903 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5903.FStar_Syntax_Syntax.n  in
                             (match uu____5902 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___385_5920 = bv1  in
                                    let uu____5921 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___385_5920.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___385_5920.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5921
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___386_5929 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____5930 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____5937 =
                                      let uu____5940 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____5940
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___386_5929.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____5930;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____5937;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___386_5929.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___386_5929.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___386_5929.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___387_5943 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___387_5943.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___387_5943.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___387_5943.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____5944 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5945 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5832
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5970 =
        let uu____5973 = cur_goal ()  in
        bind uu____5973
          (fun goal  ->
             let uu____5984 = b  in
             match uu____5984 with
             | (bv,uu____5988) ->
                 let bv' =
                   let uu____5990 =
                     let uu___388_5991 = bv  in
                     let uu____5992 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____5992;
                       FStar_Syntax_Syntax.index =
                         (uu___388_5991.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___388_5991.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____5990  in
                 let s1 =
                   let uu____5996 =
                     let uu____5997 =
                       let uu____6004 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6004)  in
                     FStar_Syntax_Syntax.NT uu____5997  in
                   [uu____5996]  in
                 let uu____6009 = subst_goal bv bv' s1 goal  in
                 (match uu____6009 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____5970
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6028 =
      let uu____6031 = cur_goal ()  in
      bind uu____6031
        (fun goal  ->
           let uu____6040 = b  in
           match uu____6040 with
           | (bv,uu____6044) ->
               let uu____6045 =
                 let uu____6054 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6054  in
               (match uu____6045 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6075 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6075 with
                     | (ty,u) ->
                         let uu____6084 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6084
                           (fun uu____6102  ->
                              match uu____6102 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___389_6112 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___389_6112.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___389_6112.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6116 =
                                      let uu____6117 =
                                        let uu____6124 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6124)  in
                                      FStar_Syntax_Syntax.NT uu____6117  in
                                    [uu____6116]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___390_6136 = b1  in
                                         let uu____6137 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___390_6136.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___390_6136.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6137
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6144  ->
                                       let new_goal =
                                         let uu____6146 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6147 =
                                           let uu____6148 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6148
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6146 uu____6147
                                          in
                                       let uu____6149 = add_goals [new_goal]
                                          in
                                       bind uu____6149
                                         (fun uu____6154  ->
                                            let uu____6155 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6155
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6028
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6178 =
        let uu____6181 = cur_goal ()  in
        bind uu____6181
          (fun goal  ->
             let uu____6190 = b  in
             match uu____6190 with
             | (bv,uu____6194) ->
                 let uu____6195 =
                   let uu____6204 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6204  in
                 (match uu____6195 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6228 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6228
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___391_6233 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___391_6233.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___391_6233.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6235 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6235))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6178
  
let (revert : unit -> unit tac) =
  fun uu____6246  ->
    let uu____6249 = cur_goal ()  in
    bind uu____6249
      (fun goal  ->
         let uu____6255 =
           let uu____6262 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6262  in
         match uu____6255 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6278 =
                 let uu____6281 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6281  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6278
                in
             let uu____6290 = new_uvar "revert" env' typ'  in
             bind uu____6290
               (fun uu____6305  ->
                  match uu____6305 with
                  | (r,u_r) ->
                      let uu____6314 =
                        let uu____6317 =
                          let uu____6318 =
                            let uu____6319 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6319.FStar_Syntax_Syntax.pos  in
                          let uu____6322 =
                            let uu____6327 =
                              let uu____6328 =
                                let uu____6335 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6335  in
                              [uu____6328]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6327  in
                          uu____6322 FStar_Pervasives_Native.None uu____6318
                           in
                        set_solution goal uu____6317  in
                      bind uu____6314
                        (fun uu____6352  ->
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
      let uu____6364 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6364
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6377 = cur_goal ()  in
    bind uu____6377
      (fun goal  ->
         mlog
           (fun uu____6385  ->
              let uu____6386 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6387 =
                let uu____6388 =
                  let uu____6389 =
                    let uu____6396 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6396  in
                  FStar_All.pipe_right uu____6389 FStar_List.length  in
                FStar_All.pipe_right uu____6388 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6386 uu____6387)
           (fun uu____6409  ->
              let uu____6410 =
                let uu____6419 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6419  in
              match uu____6410 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6458 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6458
                        then
                          let uu____6461 =
                            let uu____6462 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6462
                             in
                          fail uu____6461
                        else check1 bvs2
                     in
                  let uu____6464 =
                    let uu____6465 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6465  in
                  if uu____6464
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6469 = check1 bvs  in
                     bind uu____6469
                       (fun uu____6475  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6477 =
                            let uu____6484 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6484  in
                          bind uu____6477
                            (fun uu____6493  ->
                               match uu____6493 with
                               | (ut,uvar_ut) ->
                                   let uu____6502 = set_solution goal ut  in
                                   bind uu____6502
                                     (fun uu____6507  ->
                                        let uu____6508 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6508))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6515  ->
    let uu____6518 = cur_goal ()  in
    bind uu____6518
      (fun goal  ->
         let uu____6524 =
           let uu____6531 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6531  in
         match uu____6524 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6539) ->
             let uu____6544 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6544)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6554 = cur_goal ()  in
    bind uu____6554
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6564 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6564  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6567  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6577 = cur_goal ()  in
    bind uu____6577
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6587 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6587  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6590  -> add_goals [g']))
  
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
            let uu____6630 = FStar_Syntax_Subst.compress t  in
            uu____6630.FStar_Syntax_Syntax.n  in
          let uu____6633 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___395_6639 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___395_6639.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___395_6639.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6633
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6655 =
                   let uu____6656 = FStar_Syntax_Subst.compress t1  in
                   uu____6656.FStar_Syntax_Syntax.n  in
                 match uu____6655 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6683 = ff hd1  in
                     bind uu____6683
                       (fun hd2  ->
                          let fa uu____6705 =
                            match uu____6705 with
                            | (a,q) ->
                                let uu____6718 = ff a  in
                                bind uu____6718 (fun a1  -> ret (a1, q))
                             in
                          let uu____6731 = mapM fa args  in
                          bind uu____6731
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6797 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6797 with
                      | (bs1,t') ->
                          let uu____6806 =
                            let uu____6809 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6809 t'  in
                          bind uu____6806
                            (fun t''  ->
                               let uu____6813 =
                                 let uu____6814 =
                                   let uu____6831 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6838 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6831, uu____6838, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6814  in
                               ret uu____6813))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6907 = ff hd1  in
                     bind uu____6907
                       (fun hd2  ->
                          let ffb br =
                            let uu____6922 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6922 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6954 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6954  in
                                let uu____6955 = ff1 e  in
                                bind uu____6955
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6970 = mapM ffb brs  in
                          bind uu____6970
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7014;
                          FStar_Syntax_Syntax.lbtyp = uu____7015;
                          FStar_Syntax_Syntax.lbeff = uu____7016;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7018;
                          FStar_Syntax_Syntax.lbpos = uu____7019;_}::[]),e)
                     ->
                     let lb =
                       let uu____7044 =
                         let uu____7045 = FStar_Syntax_Subst.compress t1  in
                         uu____7045.FStar_Syntax_Syntax.n  in
                       match uu____7044 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7049) -> lb
                       | uu____7062 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7071 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7071
                         (fun def1  ->
                            ret
                              (let uu___392_7077 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___392_7077.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___392_7077.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___392_7077.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___392_7077.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___392_7077.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___392_7077.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7078 = fflb lb  in
                     bind uu____7078
                       (fun lb1  ->
                          let uu____7088 =
                            let uu____7093 =
                              let uu____7094 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7094]  in
                            FStar_Syntax_Subst.open_term uu____7093 e  in
                          match uu____7088 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7118 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7118  in
                              let uu____7119 = ff1 e1  in
                              bind uu____7119
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7160 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7160
                         (fun def  ->
                            ret
                              (let uu___393_7166 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___393_7166.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___393_7166.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___393_7166.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___393_7166.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___393_7166.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___393_7166.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7167 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7167 with
                      | (lbs1,e1) ->
                          let uu____7182 = mapM fflb lbs1  in
                          bind uu____7182
                            (fun lbs2  ->
                               let uu____7194 = ff e1  in
                               bind uu____7194
                                 (fun e2  ->
                                    let uu____7202 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7202 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7270 = ff t2  in
                     bind uu____7270
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7301 = ff t2  in
                     bind uu____7301
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7308 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___394_7315 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___394_7315.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___394_7315.FStar_Syntax_Syntax.vars)
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
            let uu____7352 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7352 with
            | (t1,lcomp,g) ->
                let uu____7364 =
                  (let uu____7367 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7367) ||
                    (let uu____7369 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7369)
                   in
                if uu____7364
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7377 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7377
                       (fun uu____7393  ->
                          match uu____7393 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7406  ->
                                    let uu____7407 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7408 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7407 uu____7408);
                               (let uu____7409 =
                                  let uu____7412 =
                                    let uu____7413 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7413 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7412
                                    opts
                                   in
                                bind uu____7409
                                  (fun uu____7416  ->
                                     let uu____7417 =
                                       bind tau
                                         (fun uu____7423  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7429  ->
                                                 let uu____7430 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7431 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7430 uu____7431);
                                            ret ut1)
                                        in
                                     focus uu____7417))))
                      in
                   let uu____7432 = trytac' rewrite_eq  in
                   bind uu____7432
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
          let uu____7630 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7630
            (fun t1  ->
               let uu____7638 =
                 f env
                   (let uu___398_7647 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___398_7647.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___398_7647.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7638
                 (fun uu____7663  ->
                    match uu____7663 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7686 =
                               let uu____7687 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7687.FStar_Syntax_Syntax.n  in
                             match uu____7686 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7720 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7720
                                   (fun uu____7745  ->
                                      match uu____7745 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7761 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7761
                                            (fun uu____7788  ->
                                               match uu____7788 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___396_7818 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___396_7818.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___396_7818.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7854 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7854 with
                                  | (bs1,t') ->
                                      let uu____7869 =
                                        let uu____7876 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7876 ctrl1 t'
                                         in
                                      bind uu____7869
                                        (fun uu____7894  ->
                                           match uu____7894 with
                                           | (t'',ctrl2) ->
                                               let uu____7909 =
                                                 let uu____7916 =
                                                   let uu___397_7919 = t4  in
                                                   let uu____7922 =
                                                     let uu____7923 =
                                                       let uu____7940 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7947 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7940,
                                                         uu____7947, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7923
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7922;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___397_7919.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___397_7919.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7916, ctrl2)  in
                                               ret uu____7909))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7994 -> ret (t3, ctrl1))))

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
              let uu____8037 = ctrl_tac_fold f env ctrl t  in
              bind uu____8037
                (fun uu____8061  ->
                   match uu____8061 with
                   | (t1,ctrl1) ->
                       let uu____8076 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8076
                         (fun uu____8103  ->
                            match uu____8103 with
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
              let uu____8185 =
                let uu____8192 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8192
                  (fun uu____8201  ->
                     let uu____8202 = ctrl t1  in
                     bind uu____8202
                       (fun res  ->
                          let uu____8225 = trivial ()  in
                          bind uu____8225 (fun uu____8233  -> ret res)))
                 in
              bind uu____8185
                (fun uu____8249  ->
                   match uu____8249 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8273 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8273 with
                          | (t2,lcomp,g) ->
                              let uu____8289 =
                                (let uu____8292 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8292) ||
                                  (let uu____8294 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8294)
                                 in
                              if uu____8289
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8307 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8307
                                   (fun uu____8327  ->
                                      match uu____8327 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8344  ->
                                                let uu____8345 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8346 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8345 uu____8346);
                                           (let uu____8347 =
                                              let uu____8350 =
                                                let uu____8351 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8351 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8350 opts
                                               in
                                            bind uu____8347
                                              (fun uu____8358  ->
                                                 let uu____8359 =
                                                   bind rewriter
                                                     (fun uu____8373  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8379  ->
                                                             let uu____8380 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8381 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8380
                                                               uu____8381);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8359)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8422 =
        bind get
          (fun ps  ->
             let uu____8432 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8432 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8469  ->
                       let uu____8470 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8470);
                  bind dismiss_all
                    (fun uu____8473  ->
                       let uu____8474 =
                         let uu____8481 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8481
                           keepGoing gt1
                          in
                       bind uu____8474
                         (fun uu____8493  ->
                            match uu____8493 with
                            | (gt',uu____8501) ->
                                (log ps
                                   (fun uu____8505  ->
                                      let uu____8506 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8506);
                                 (let uu____8507 = push_goals gs  in
                                  bind uu____8507
                                    (fun uu____8512  ->
                                       let uu____8513 =
                                         let uu____8516 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8516]  in
                                       add_goals uu____8513)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8422
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8539 =
        bind get
          (fun ps  ->
             let uu____8549 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8549 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8586  ->
                       let uu____8587 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8587);
                  bind dismiss_all
                    (fun uu____8590  ->
                       let uu____8591 =
                         let uu____8594 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8594 gt1
                          in
                       bind uu____8591
                         (fun gt'  ->
                            log ps
                              (fun uu____8602  ->
                                 let uu____8603 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8603);
                            (let uu____8604 = push_goals gs  in
                             bind uu____8604
                               (fun uu____8609  ->
                                  let uu____8610 =
                                    let uu____8613 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8613]  in
                                  add_goals uu____8610))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8539
  
let (trefl : unit -> unit tac) =
  fun uu____8624  ->
    let uu____8627 =
      let uu____8630 = cur_goal ()  in
      bind uu____8630
        (fun g  ->
           let uu____8648 =
             let uu____8653 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8653  in
           match uu____8648 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8661 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8661 with
                | (hd1,args) ->
                    let uu____8694 =
                      let uu____8705 =
                        let uu____8706 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8706.FStar_Syntax_Syntax.n  in
                      (uu____8705, args)  in
                    (match uu____8694 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8718::(l,uu____8720)::(r,uu____8722)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8749 =
                           let uu____8752 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8752 l r  in
                         bind uu____8749
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8759 =
                                  let uu____8760 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8760 l  in
                                let uu____8761 =
                                  let uu____8762 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8762 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8759 uu____8761
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8765) ->
                         let uu____8778 =
                           let uu____8779 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8779 t  in
                         fail1 "trefl: not an equality (%s)" uu____8778))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8627
  
let (dup : unit -> unit tac) =
  fun uu____8792  ->
    let uu____8795 = cur_goal ()  in
    bind uu____8795
      (fun g  ->
         let uu____8801 =
           let uu____8808 = FStar_Tactics_Types.goal_env g  in
           let uu____8809 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8808 uu____8809  in
         bind uu____8801
           (fun uu____8818  ->
              match uu____8818 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___399_8828 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___399_8828.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___399_8828.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___399_8828.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8831  ->
                       let uu____8832 =
                         let uu____8835 = FStar_Tactics_Types.goal_env g  in
                         let uu____8836 =
                           let uu____8837 =
                             let uu____8838 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8839 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8838
                               uu____8839
                              in
                           let uu____8840 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8841 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8837 uu____8840 u
                             uu____8841
                            in
                         add_irrelevant_goal "dup equation" uu____8835
                           uu____8836 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8832
                         (fun uu____8844  ->
                            let uu____8845 = add_goals [g']  in
                            bind uu____8845 (fun uu____8849  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8856  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___400_8873 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___400_8873.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___400_8873.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___400_8873.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___400_8873.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___400_8873.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___400_8873.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___400_8873.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___400_8873.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___400_8873.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___400_8873.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___400_8873.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____8874 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8883  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___401_8896 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___401_8896.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___401_8896.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___401_8896.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___401_8896.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___401_8896.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___401_8896.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___401_8896.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___401_8896.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___401_8896.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___401_8896.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___401_8896.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8903  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8910 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8930 =
      let uu____8937 = cur_goal ()  in
      bind uu____8937
        (fun g  ->
           let uu____8947 =
             let uu____8956 = FStar_Tactics_Types.goal_env g  in
             __tc uu____8956 t  in
           bind uu____8947
             (fun uu____8984  ->
                match uu____8984 with
                | (t1,typ,guard) ->
                    let uu____9000 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9000 with
                     | (hd1,args) ->
                         let uu____9043 =
                           let uu____9056 =
                             let uu____9057 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9057.FStar_Syntax_Syntax.n  in
                           (uu____9056, args)  in
                         (match uu____9043 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9076)::(q,uu____9078)::[]) when
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
                                let uu____9116 =
                                  let uu____9117 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9117
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9116
                                 in
                              let g2 =
                                let uu____9119 =
                                  let uu____9120 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9120
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9119
                                 in
                              bind __dismiss
                                (fun uu____9127  ->
                                   let uu____9128 = add_goals [g1; g2]  in
                                   bind uu____9128
                                     (fun uu____9137  ->
                                        let uu____9138 =
                                          let uu____9143 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9144 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9143, uu____9144)  in
                                        ret uu____9138))
                          | uu____9149 ->
                              let uu____9162 =
                                let uu____9163 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9163 typ  in
                              fail1 "Not a disjunction: %s" uu____9162))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8930
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9193 =
      let uu____9196 = cur_goal ()  in
      bind uu____9196
        (fun g  ->
           FStar_Options.push ();
           (let uu____9209 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9209);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___402_9216 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___402_9216.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___402_9216.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___402_9216.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9193
  
let (top_env : unit -> env tac) =
  fun uu____9228  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9241  ->
    let uu____9244 = cur_goal ()  in
    bind uu____9244
      (fun g  ->
         let uu____9250 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9250)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9259  ->
    let uu____9262 = cur_goal ()  in
    bind uu____9262
      (fun g  ->
         let uu____9268 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9268)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9277  ->
    let uu____9280 = cur_goal ()  in
    bind uu____9280
      (fun g  ->
         let uu____9286 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9286)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9303 =
        mlog
          (fun uu____9308  ->
             let uu____9309 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9309)
          (fun uu____9312  ->
             let uu____9313 = cur_goal ()  in
             bind uu____9313
               (fun goal  ->
                  let env =
                    let uu____9321 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9321 ty  in
                  let uu____9322 = __tc env tm  in
                  bind uu____9322
                    (fun uu____9341  ->
                       match uu____9341 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9355  ->
                                let uu____9356 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9356)
                             (fun uu____9358  ->
                                mlog
                                  (fun uu____9361  ->
                                     let uu____9362 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9362)
                                  (fun uu____9365  ->
                                     let uu____9366 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9366
                                       (fun uu____9370  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9303
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9393 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9399 =
              let uu____9406 =
                let uu____9407 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9407
                 in
              new_uvar "uvar_env.2" env uu____9406  in
            bind uu____9399
              (fun uu____9423  ->
                 match uu____9423 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9393
        (fun typ  ->
           let uu____9435 = new_uvar "uvar_env" env typ  in
           bind uu____9435
             (fun uu____9449  -> match uu____9449 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9467 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9486 -> g.FStar_Tactics_Types.opts
             | uu____9489 -> FStar_Options.peek ()  in
           let uu____9492 = FStar_Syntax_Util.head_and_args t  in
           match uu____9492 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9510);
                FStar_Syntax_Syntax.pos = uu____9511;
                FStar_Syntax_Syntax.vars = uu____9512;_},uu____9513)
               ->
               let env1 =
                 let uu___403_9551 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___403_9551.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___403_9551.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___403_9551.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___403_9551.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___403_9551.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___403_9551.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___403_9551.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___403_9551.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___403_9551.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___403_9551.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___403_9551.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___403_9551.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___403_9551.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___403_9551.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___403_9551.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___403_9551.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___403_9551.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___403_9551.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___403_9551.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___403_9551.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___403_9551.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___403_9551.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___403_9551.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___403_9551.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___403_9551.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___403_9551.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___403_9551.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___403_9551.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___403_9551.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___403_9551.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___403_9551.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___403_9551.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___403_9551.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___403_9551.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___403_9551.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___403_9551.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___403_9551.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___403_9551.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___403_9551.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9553 =
                 let uu____9556 = bnorm_goal g  in [uu____9556]  in
               add_goals uu____9553
           | uu____9557 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9467
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9604 = if b then t2 else ret false  in
             bind uu____9604 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____9615 = trytac comp  in
      bind uu____9615
        (fun uu___343_9623  ->
           match uu___343_9623 with
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
        let uu____9649 =
          bind get
            (fun ps  ->
               let uu____9655 = __tc e t1  in
               bind uu____9655
                 (fun uu____9675  ->
                    match uu____9675 with
                    | (t11,ty1,g1) ->
                        let uu____9687 = __tc e t2  in
                        bind uu____9687
                          (fun uu____9707  ->
                             match uu____9707 with
                             | (t21,ty2,g2) ->
                                 let uu____9719 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____9719
                                   (fun uu____9724  ->
                                      let uu____9725 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____9725
                                        (fun uu____9731  ->
                                           let uu____9732 =
                                             do_unify e ty1 ty2  in
                                           let uu____9735 =
                                             do_unify e t11 t21  in
                                           tac_and uu____9732 uu____9735)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____9649
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9768  ->
             let uu____9769 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9769
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
        (fun uu____9790  ->
           let uu____9791 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9791)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9801 =
      mlog
        (fun uu____9806  ->
           let uu____9807 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9807)
        (fun uu____9810  ->
           let uu____9811 = cur_goal ()  in
           bind uu____9811
             (fun g  ->
                let uu____9817 =
                  let uu____9826 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9826 ty  in
                bind uu____9817
                  (fun uu____9838  ->
                     match uu____9838 with
                     | (ty1,uu____9848,guard) ->
                         let uu____9850 =
                           let uu____9853 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9853 guard  in
                         bind uu____9850
                           (fun uu____9856  ->
                              let uu____9857 =
                                let uu____9860 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9861 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9860 uu____9861 ty1  in
                              bind uu____9857
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9867 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9867
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
                                        let uu____9873 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9874 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9873 uu____9874
                                         in
                                      let nty =
                                        let uu____9876 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9876 ty1  in
                                      let uu____9877 =
                                        let uu____9880 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9880 ng nty  in
                                      bind uu____9877
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9886 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9886
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9801
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9908::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9936 = init xs  in x :: uu____9936
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9948 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9956) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10013 = last args  in
          (match uu____10013 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10035 =
                 let uu____10036 =
                   let uu____10041 =
                     let uu____10042 =
                       let uu____10047 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10047  in
                     uu____10042 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10041, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10036  in
               FStar_All.pipe_left ret uu____10035)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10058,uu____10059) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10103 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10103 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10136 =
                      let uu____10137 =
                        let uu____10142 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10142)  in
                      FStar_Reflection_Data.Tv_Abs uu____10137  in
                    FStar_All.pipe_left ret uu____10136))
      | FStar_Syntax_Syntax.Tm_type uu____10145 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10165 ->
          let uu____10178 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10178 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10208 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10208 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10247 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10255 =
            let uu____10256 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10256  in
          FStar_All.pipe_left ret uu____10255
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10277 =
            let uu____10278 =
              let uu____10283 =
                let uu____10284 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10284  in
              (uu____10283, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10278  in
          FStar_All.pipe_left ret uu____10277
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10318 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10323 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10323 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10362 ->
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
             | FStar_Util.Inr uu____10392 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10396 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10396 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10416 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10420 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10474 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10474
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10493 =
                  let uu____10500 =
                    FStar_List.map
                      (fun uu____10512  ->
                         match uu____10512 with
                         | (p1,uu____10520) -> inspect_pat p1) ps
                     in
                  (fv, uu____10500)  in
                FStar_Reflection_Data.Pat_Cons uu____10493
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
              (fun uu___344_10614  ->
                 match uu___344_10614 with
                 | (pat,uu____10636,t4) ->
                     let uu____10654 = inspect_pat pat  in (uu____10654, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10663 ->
          ((let uu____10665 =
              let uu____10670 =
                let uu____10671 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10672 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10671 uu____10672
                 in
              (FStar_Errors.Warning_CantInspect, uu____10670)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10665);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9948
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10685 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10685
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10689 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10689
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10693 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10693
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10700 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10700
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10719 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10719
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10732 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10732
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10747 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10747
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10751 =
          let uu____10752 =
            let uu____10759 =
              let uu____10760 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10760  in
            FStar_Syntax_Syntax.mk uu____10759  in
          uu____10752 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10751
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10768 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10768
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10777 =
          let uu____10778 =
            let uu____10785 =
              let uu____10786 =
                let uu____10799 =
                  let uu____10802 =
                    let uu____10803 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10803]  in
                  FStar_Syntax_Subst.close uu____10802 t2  in
                ((false, [lb]), uu____10799)  in
              FStar_Syntax_Syntax.Tm_let uu____10786  in
            FStar_Syntax_Syntax.mk uu____10785  in
          uu____10778 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10777
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10837 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10837 with
         | (lbs,body) ->
             let uu____10852 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10852)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10886 =
                let uu____10887 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10887  in
              FStar_All.pipe_left wrap uu____10886
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10894 =
                let uu____10895 =
                  let uu____10908 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10924 = pack_pat p1  in
                         (uu____10924, false)) ps
                     in
                  (fv, uu____10908)  in
                FStar_Syntax_Syntax.Pat_cons uu____10895  in
              FStar_All.pipe_left wrap uu____10894
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
            (fun uu___345_10970  ->
               match uu___345_10970 with
               | (pat,t1) ->
                   let uu____10987 = pack_pat pat  in
                   (uu____10987, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11035 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11035
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11063 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11063
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11109 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11109
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11148 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11148
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11169 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11169 with
      | (u,ctx_uvars,g_u) ->
          let uu____11201 = FStar_List.hd ctx_uvars  in
          (match uu____11201 with
           | (ctx_uvar,uu____11215) ->
               let g =
                 let uu____11217 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11217 false
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
        let uu____11237 = goal_of_goal_ty env typ  in
        match uu____11237 with
        | (g,g_u) ->
            let ps =
              let uu____11249 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11249
              }  in
            let uu____11254 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11254)
  