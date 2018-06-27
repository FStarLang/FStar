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
        let p_imp imp =
          FStar_Syntax_Print.uvar_to_string
            (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
           in
        let uu____491 =
          let uu____494 =
            let uu____495 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____495 msg
             in
          let uu____496 =
            let uu____499 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____500 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____500
              else ""  in
            let uu____502 =
              let uu____505 =
                let uu____506 =
                  FStar_TypeChecker_Env.debug
                    ps.FStar_Tactics_Types.main_context
                    (FStar_Options.Other "Imp")
                   in
                if uu____506
                then
                  let uu____507 =
                    FStar_Common.string_of_list p_imp
                      ps.FStar_Tactics_Types.all_implicits
                     in
                  FStar_Util.format1 "Imps: %s\n" uu____507
                else ""  in
              let uu____509 =
                let uu____512 =
                  let uu____513 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.goals)
                     in
                  let uu____514 =
                    let uu____515 =
                      FStar_List.map (goal_to_string ps)
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_String.concat "\n" uu____515  in
                  FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____513
                    uu____514
                   in
                let uu____518 =
                  let uu____521 =
                    let uu____522 =
                      FStar_Util.string_of_int
                        (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                       in
                    let uu____523 =
                      let uu____524 =
                        FStar_List.map (goal_to_string ps)
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_String.concat "\n" uu____524  in
                    FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____522
                      uu____523
                     in
                  [uu____521]  in
                uu____512 :: uu____518  in
              uu____505 :: uu____509  in
            uu____499 :: uu____502  in
          uu____494 :: uu____496  in
        FStar_String.concat "" uu____491
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____533 =
        let uu____534 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____534  in
      let uu____535 =
        let uu____540 =
          let uu____541 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____541  in
        FStar_Syntax_Print.binders_to_json uu____540  in
      FStar_All.pipe_right uu____533 uu____535  in
    let uu____542 =
      let uu____549 =
        let uu____556 =
          let uu____561 =
            let uu____562 =
              let uu____569 =
                let uu____574 =
                  let uu____575 =
                    let uu____576 = FStar_Tactics_Types.goal_env g  in
                    let uu____577 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____576 uu____577  in
                  FStar_Util.JsonStr uu____575  in
                ("witness", uu____574)  in
              let uu____578 =
                let uu____585 =
                  let uu____590 =
                    let uu____591 =
                      let uu____592 = FStar_Tactics_Types.goal_env g  in
                      let uu____593 = FStar_Tactics_Types.goal_type g  in
                      tts uu____592 uu____593  in
                    FStar_Util.JsonStr uu____591  in
                  ("type", uu____590)  in
                [uu____585]  in
              uu____569 :: uu____578  in
            FStar_Util.JsonAssoc uu____562  in
          ("goal", uu____561)  in
        [uu____556]  in
      ("hyps", g_binders) :: uu____549  in
    FStar_Util.JsonAssoc uu____542
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____626  ->
    match uu____626 with
    | (msg,ps) ->
        let uu____633 =
          let uu____640 =
            let uu____647 =
              let uu____654 =
                let uu____661 =
                  let uu____666 =
                    let uu____667 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____667  in
                  ("goals", uu____666)  in
                let uu____670 =
                  let uu____677 =
                    let uu____682 =
                      let uu____683 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____683  in
                    ("smt-goals", uu____682)  in
                  [uu____677]  in
                uu____661 :: uu____670  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____654
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____647  in
          let uu____706 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____719 =
                let uu____724 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____724)  in
              [uu____719]
            else []  in
          FStar_List.append uu____640 uu____706  in
        FStar_Util.JsonAssoc uu____633
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____754  ->
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
         (let uu____777 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____777 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Cfg.psc_subst psc  in
         (let uu____795 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____795 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____849 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____849
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____857 . Prims.string -> Prims.string -> 'Auu____857 tac =
  fun msg  ->
    fun x  -> let uu____870 = FStar_Util.format1 msg x  in fail uu____870
  
let fail2 :
  'Auu____879 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____879 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____897 = FStar_Util.format2 msg x y  in fail uu____897
  
let fail3 :
  'Auu____908 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____908 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____931 = FStar_Util.format3 msg x y z  in fail uu____931
  
let fail4 :
  'Auu____944 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____944 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____972 = FStar_Util.format4 msg x y z w  in fail uu____972
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1005 = run t ps  in
         match uu____1005 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___349_1029 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___349_1029.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___349_1029.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___349_1029.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___349_1029.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___349_1029.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___349_1029.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___349_1029.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___349_1029.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___349_1029.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___349_1029.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (uu___349_1029.FStar_Tactics_Types.tac_verb_dbg)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1056 = trytac' t  in
    bind uu____1056
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1083 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1119 = trytac t  in run uu____1119 ps
         with
         | FStar_Errors.Err (uu____1135,msg) ->
             (log ps
                (fun uu____1139  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1144,msg,uu____1146) ->
             (log ps
                (fun uu____1149  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1182 = run t ps  in
           match uu____1182 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1201  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1222 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1222
         then
           let uu____1223 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1224 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1223
             uu____1224
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1236 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1236
            then
              let uu____1237 = FStar_Util.string_of_bool res  in
              let uu____1238 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1239 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1237 uu____1238 uu____1239
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1247,msg) ->
             mlog
               (fun uu____1250  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1252  -> ret false)
         | FStar_Errors.Error (uu____1253,msg,r) ->
             mlog
               (fun uu____1258  ->
                  let uu____1259 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1259) (fun uu____1261  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1284  ->
             (let uu____1286 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1286
              then
                (FStar_Options.push ();
                 (let uu____1288 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1290 = __do_unify env t1 t2  in
              bind uu____1290
                (fun r  ->
                   (let uu____1297 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1297 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___354_1305 = ps  in
         let uu____1306 =
           FStar_List.filter
             (fun g  ->
                let uu____1312 = check_goal_solved g  in
                FStar_Option.isNone uu____1312) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___354_1305.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___354_1305.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___354_1305.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1306;
           FStar_Tactics_Types.smt_goals =
             (uu___354_1305.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___354_1305.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___354_1305.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___354_1305.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___354_1305.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___354_1305.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___354_1305.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___354_1305.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1329 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1329 with
      | FStar_Pervasives_Native.Some uu____1334 ->
          let uu____1335 =
            let uu____1336 = goal_to_string_verbose goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1336  in
          fail uu____1335
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1352 = FStar_Tactics_Types.goal_env goal  in
      let uu____1353 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1352 solution uu____1353
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1359 =
         let uu___355_1360 = p  in
         let uu____1361 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___355_1360.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___355_1360.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___355_1360.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1361;
           FStar_Tactics_Types.smt_goals =
             (uu___355_1360.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___355_1360.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___355_1360.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___355_1360.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___355_1360.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___355_1360.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___355_1360.FStar_Tactics_Types.freshness);
           FStar_Tactics_Types.tac_verb_dbg =
             (uu___355_1360.FStar_Tactics_Types.tac_verb_dbg)
         }  in
       set uu____1359)
  
let (dismiss : unit -> unit tac) =
  fun uu____1370  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1377 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1398  ->
           let uu____1399 =
             let uu____1400 = FStar_Tactics_Types.goal_witness goal  in
             FStar_Syntax_Print.term_to_string uu____1400  in
           let uu____1401 = FStar_Syntax_Print.term_to_string solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1399 uu____1401)
        (fun uu____1404  ->
           let uu____1405 = trysolve goal solution  in
           bind uu____1405
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1413  -> remove_solved_goals)
                else
                  (let uu____1415 =
                     let uu____1416 =
                       let uu____1417 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1417 solution  in
                     let uu____1418 =
                       let uu____1419 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1420 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1419 uu____1420  in
                     let uu____1421 =
                       let uu____1422 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1423 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1422 uu____1423  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1416 uu____1418 uu____1421
                      in
                   fail uu____1415)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1438 = set_solution goal solution  in
      bind uu____1438
        (fun uu____1442  ->
           bind __dismiss (fun uu____1444  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___356_1451 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___356_1451.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___356_1451.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___356_1451.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___356_1451.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___356_1451.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___356_1451.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___356_1451.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___356_1451.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___356_1451.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___356_1451.FStar_Tactics_Types.freshness);
            FStar_Tactics_Types.tac_verb_dbg =
              (uu___356_1451.FStar_Tactics_Types.tac_verb_dbg)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1470 = FStar_Options.defensive ()  in
    if uu____1470
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1475 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1475)
         in
      let b2 =
        b1 &&
          (let uu____1478 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1478)
         in
      let rec aux b3 e =
        let uu____1490 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1490 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1508 =
        (let uu____1511 = aux b2 env  in Prims.op_Negation uu____1511) &&
          (let uu____1513 = FStar_ST.op_Bang nwarn  in
           uu____1513 < (Prims.parse_int "5"))
         in
      (if uu____1508
       then
         ((let uu____1534 =
             let uu____1535 = FStar_Tactics_Types.goal_type g  in
             uu____1535.FStar_Syntax_Syntax.pos  in
           let uu____1538 =
             let uu____1543 =
               let uu____1544 = goal_to_string_verbose g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1544
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1543)  in
           FStar_Errors.log_issue uu____1534 uu____1538);
          (let uu____1545 =
             let uu____1546 = FStar_ST.op_Bang nwarn  in
             uu____1546 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1545))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___357_1606 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___357_1606.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___357_1606.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___357_1606.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___357_1606.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___357_1606.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___357_1606.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___357_1606.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___357_1606.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___357_1606.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___357_1606.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___357_1606.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___358_1626 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___358_1626.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___358_1626.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___358_1626.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___358_1626.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___358_1626.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___358_1626.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___358_1626.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___358_1626.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___358_1626.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___358_1626.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___358_1626.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___359_1646 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___359_1646.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___359_1646.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___359_1646.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___359_1646.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___359_1646.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___359_1646.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___359_1646.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___359_1646.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___359_1646.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___359_1646.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___359_1646.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___360_1666 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___360_1666.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___360_1666.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___360_1666.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___360_1666.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___360_1666.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___360_1666.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___360_1666.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___360_1666.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___360_1666.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___360_1666.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___360_1666.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1677  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___361_1691 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___361_1691.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___361_1691.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___361_1691.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___361_1691.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___361_1691.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___361_1691.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___361_1691.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___361_1691.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___361_1691.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___361_1691.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___361_1691.FStar_Tactics_Types.tac_verb_dbg)
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
        let uu____1719 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1719 with
        | (u,ctx_uvar,g_u) ->
            let uu____1753 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1753
              (fun uu____1762  ->
                 let uu____1763 =
                   let uu____1768 =
                     let uu____1769 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1769  in
                   (u, uu____1768)  in
                 ret uu____1763)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1787 = FStar_Syntax_Util.un_squash t  in
    match uu____1787 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1797 =
          let uu____1798 = FStar_Syntax_Subst.compress t'  in
          uu____1798.FStar_Syntax_Syntax.n  in
        (match uu____1797 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1802 -> false)
    | uu____1803 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1813 = FStar_Syntax_Util.un_squash t  in
    match uu____1813 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1823 =
          let uu____1824 = FStar_Syntax_Subst.compress t'  in
          uu____1824.FStar_Syntax_Syntax.n  in
        (match uu____1823 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1828 -> false)
    | uu____1829 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1840  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1851 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1851 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1858 = goal_to_string_verbose hd1  in
                    let uu____1859 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1858 uu____1859);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1866  ->
    let uu____1869 =
      bind get
        (fun ps  ->
           let uu____1875 = cur_goal ()  in
           bind uu____1875
             (fun g  ->
                (let uu____1882 =
                   let uu____1883 = FStar_Tactics_Types.goal_type g  in
                   uu____1883.FStar_Syntax_Syntax.pos  in
                 let uu____1886 =
                   let uu____1891 =
                     let uu____1892 = goal_to_string ps g  in
                     FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                       uu____1892
                      in
                   (FStar_Errors.Warning_TacAdmit, uu____1891)  in
                 FStar_Errors.log_issue uu____1882 uu____1886);
                solve' g FStar_Syntax_Util.exp_unit))
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1869
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1903  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___362_1913 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___362_1913.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___362_1913.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___362_1913.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___362_1913.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___362_1913.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___362_1913.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___362_1913.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___362_1913.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___362_1913.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___362_1913.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"));
             FStar_Tactics_Types.tac_verb_dbg =
               (uu___362_1913.FStar_Tactics_Types.tac_verb_dbg)
           }  in
         let uu____1914 = set ps1  in
         bind uu____1914
           (fun uu____1919  ->
              let uu____1920 = FStar_BigInt.of_int_fs n1  in ret uu____1920))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1927  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1935 = FStar_BigInt.of_int_fs n1  in ret uu____1935)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1948  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1956 = FStar_BigInt.of_int_fs n1  in ret uu____1956)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1969  ->
    let uu____1972 = cur_goal ()  in
    bind uu____1972 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2004 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2004 phi  in
          let uu____2005 = new_uvar reason env typ  in
          bind uu____2005
            (fun uu____2020  ->
               match uu____2020 with
               | (uu____2027,ctx_uvar) ->
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
             (fun uu____2072  ->
                let uu____2073 = FStar_Syntax_Print.term_to_string t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2073)
             (fun uu____2076  ->
                let e1 =
                  let uu___363_2078 = e  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___363_2078.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___363_2078.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___363_2078.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___363_2078.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___363_2078.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___363_2078.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___363_2078.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___363_2078.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___363_2078.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___363_2078.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.is_pattern =
                      (uu___363_2078.FStar_TypeChecker_Env.is_pattern);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___363_2078.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___363_2078.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___363_2078.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___363_2078.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___363_2078.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___363_2078.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___363_2078.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.is_iface =
                      (uu___363_2078.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___363_2078.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___363_2078.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___363_2078.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___363_2078.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___363_2078.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___363_2078.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.tc_term =
                      (uu___363_2078.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___363_2078.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___363_2078.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___363_2078.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___363_2078.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___363_2078.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___363_2078.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___363_2078.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___363_2078.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___363_2078.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___363_2078.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___363_2078.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___363_2078.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___363_2078.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.dep_graph =
                      (uu___363_2078.FStar_TypeChecker_Env.dep_graph);
                    FStar_TypeChecker_Env.nbe =
                      (uu___363_2078.FStar_TypeChecker_Env.nbe)
                  }  in
                try
                  let uu____2098 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e1 t
                     in
                  ret uu____2098
                with
                | FStar_Errors.Err (uu____2125,msg) ->
                    let uu____2127 = tts e1 t  in
                    let uu____2128 =
                      let uu____2129 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2129
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2127 uu____2128 msg
                | FStar_Errors.Error (uu____2136,msg,uu____2138) ->
                    let uu____2139 = tts e1 t  in
                    let uu____2140 =
                      let uu____2141 = FStar_TypeChecker_Env.all_binders e1
                         in
                      FStar_All.pipe_right uu____2141
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2139 uu____2140 msg))
  
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
  fun uu____2168  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___366_2186 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___366_2186.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___366_2186.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___366_2186.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___366_2186.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___366_2186.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___366_2186.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___366_2186.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___366_2186.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___366_2186.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___366_2186.FStar_Tactics_Types.freshness);
              FStar_Tactics_Types.tac_verb_dbg =
                (uu___366_2186.FStar_Tactics_Types.tac_verb_dbg)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2210 = get_guard_policy ()  in
      bind uu____2210
        (fun old_pol  ->
           let uu____2216 = set_guard_policy pol  in
           bind uu____2216
             (fun uu____2220  ->
                bind t
                  (fun r  ->
                     let uu____2224 = set_guard_policy old_pol  in
                     bind uu____2224 (fun uu____2228  -> ret r))))
  
let (getopts : FStar_Options.optionstate tac) =
  let uu____2231 = let uu____2236 = cur_goal ()  in trytac uu____2236  in
  bind uu____2231
    (fun uu___339_2243  ->
       match uu___339_2243 with
       | FStar_Pervasives_Native.Some g -> ret g.FStar_Tactics_Types.opts
       | FStar_Pervasives_Native.None  ->
           let uu____2249 = FStar_Options.peek ()  in ret uu____2249)
  
let (proc_guard :
  Prims.string -> env -> FStar_TypeChecker_Env.guard_t -> unit tac) =
  fun reason  ->
    fun e  ->
      fun g  ->
        bind getopts
          (fun opts  ->
             let uu____2272 =
               let uu____2273 = FStar_TypeChecker_Rel.simplify_guard e g  in
               uu____2273.FStar_TypeChecker_Env.guard_f  in
             match uu____2272 with
             | FStar_TypeChecker_Common.Trivial  -> ret ()
             | FStar_TypeChecker_Common.NonTrivial f ->
                 let uu____2277 = istrivial e f  in
                 if uu____2277
                 then ret ()
                 else
                   bind get
                     (fun ps  ->
                        match ps.FStar_Tactics_Types.guard_policy with
                        | FStar_Tactics_Types.Drop  -> ret ()
                        | FStar_Tactics_Types.Goal  ->
                            let uu____2285 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2285
                              (fun goal  ->
                                 let goal1 =
                                   let uu___367_2292 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___367_2292.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___367_2292.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___367_2292.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_goals [goal1])
                        | FStar_Tactics_Types.SMT  ->
                            let uu____2293 =
                              mk_irrelevant_goal reason e f opts  in
                            bind uu____2293
                              (fun goal  ->
                                 let goal1 =
                                   let uu___368_2300 = goal  in
                                   {
                                     FStar_Tactics_Types.goal_main_env =
                                       (uu___368_2300.FStar_Tactics_Types.goal_main_env);
                                     FStar_Tactics_Types.goal_ctx_uvar =
                                       (uu___368_2300.FStar_Tactics_Types.goal_ctx_uvar);
                                     FStar_Tactics_Types.opts =
                                       (uu___368_2300.FStar_Tactics_Types.opts);
                                     FStar_Tactics_Types.is_guard = true
                                   }  in
                                 push_smt_goals [goal1])
                        | FStar_Tactics_Types.Force  ->
                            (try
                               let uu____2308 =
                                 let uu____2309 =
                                   let uu____2310 =
                                     FStar_TypeChecker_Rel.discharge_guard_no_smt
                                       e g
                                      in
                                   FStar_All.pipe_left
                                     FStar_TypeChecker_Env.is_trivial
                                     uu____2310
                                    in
                                 Prims.op_Negation uu____2309  in
                               if uu____2308
                               then
                                 mlog
                                   (fun uu____2315  ->
                                      let uu____2316 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2316)
                                   (fun uu____2318  ->
                                      fail1 "Forcing the guard failed %s)"
                                        reason)
                               else ret ()
                             with
                             | uu____2325 ->
                                 mlog
                                   (fun uu____2328  ->
                                      let uu____2329 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          e g
                                         in
                                      FStar_Util.print1 "guard = %s\n"
                                        uu____2329)
                                   (fun uu____2331  ->
                                      fail1 "Forcing the guard failed (%s)"
                                        reason))))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2341 =
      let uu____2344 = cur_goal ()  in
      bind uu____2344
        (fun goal  ->
           let uu____2350 =
             let uu____2359 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2359 t  in
           bind uu____2350
             (fun uu____2371  ->
                match uu____2371 with
                | (t1,typ,guard) ->
                    let uu____2383 =
                      let uu____2386 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2386 guard  in
                    bind uu____2383 (fun uu____2388  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2341
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2417 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2417 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2428  ->
    let uu____2431 = cur_goal ()  in
    bind uu____2431
      (fun goal  ->
         let uu____2437 =
           let uu____2438 = FStar_Tactics_Types.goal_env goal  in
           let uu____2439 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2438 uu____2439  in
         if uu____2437
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2443 =
              let uu____2444 = FStar_Tactics_Types.goal_env goal  in
              let uu____2445 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2444 uu____2445  in
            fail1 "Not a trivial goal: %s" uu____2443))
  
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
          let uu____2474 =
            let uu____2475 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2475.FStar_TypeChecker_Env.guard_f  in
          match uu____2474 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2483 = istrivial e f  in
              if uu____2483
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2491 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2491
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___371_2501 = goal  in
                            {
                              FStar_Tactics_Types.goal_main_env =
                                (uu___371_2501.FStar_Tactics_Types.goal_main_env);
                              FStar_Tactics_Types.goal_ctx_uvar =
                                (uu___371_2501.FStar_Tactics_Types.goal_ctx_uvar);
                              FStar_Tactics_Types.opts =
                                (uu___371_2501.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2508  ->
    let uu____2511 = cur_goal ()  in
    bind uu____2511
      (fun g  ->
         let uu____2517 = is_irrelevant g  in
         if uu____2517
         then bind __dismiss (fun uu____2521  -> add_smt_goals [g])
         else
           (let uu____2523 =
              let uu____2524 = FStar_Tactics_Types.goal_env g  in
              let uu____2525 = FStar_Tactics_Types.goal_type g  in
              tts uu____2524 uu____2525  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2523))
  
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
             let uu____2574 =
               try
                 let uu____2608 =
                   let uu____2617 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2617 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2608
               with | uu____2639 -> fail "divide: not enough goals"  in
             bind uu____2574
               (fun uu____2665  ->
                  match uu____2665 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___372_2691 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___372_2691.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___372_2691.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___372_2691.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___372_2691.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___372_2691.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___372_2691.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___372_2691.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___372_2691.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___372_2691.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (uu___372_2691.FStar_Tactics_Types.tac_verb_dbg)
                        }  in
                      let uu____2692 = set lp  in
                      bind uu____2692
                        (fun uu____2700  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let rp =
                                       let uu___373_2716 = lp'  in
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (uu___373_2716.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.main_goal =
                                           (uu___373_2716.FStar_Tactics_Types.main_goal);
                                         FStar_Tactics_Types.all_implicits =
                                           (uu___373_2716.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (uu___373_2716.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (uu___373_2716.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (uu___373_2716.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (uu___373_2716.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (uu___373_2716.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (uu___373_2716.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (uu___373_2716.FStar_Tactics_Types.tac_verb_dbg)
                                       }  in
                                     let uu____2717 = set rp  in
                                     bind uu____2717
                                       (fun uu____2725  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___374_2741 = rp'
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___374_2741.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (uu___374_2741.FStar_Tactics_Types.tac_verb_dbg)
                                                      }  in
                                                    let uu____2742 = set p'
                                                       in
                                                    bind uu____2742
                                                      (fun uu____2750  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2756 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2777 = divide FStar_BigInt.one f idtac  in
    bind uu____2777
      (fun uu____2790  -> match uu____2790 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2827::uu____2828 ->
             let uu____2831 =
               let uu____2840 = map tau  in
               divide FStar_BigInt.one tau uu____2840  in
             bind uu____2831
               (fun uu____2858  ->
                  match uu____2858 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2899 =
        bind t1
          (fun uu____2904  ->
             let uu____2905 = map t2  in
             bind uu____2905 (fun uu____2913  -> ret ()))
         in
      focus uu____2899
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2922  ->
    let uu____2925 =
      let uu____2928 = cur_goal ()  in
      bind uu____2928
        (fun goal  ->
           let uu____2937 =
             let uu____2944 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____2944  in
           match uu____2937 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2953 =
                 let uu____2954 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2954  in
               if uu____2953
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____2959 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____2959 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____2973 = new_uvar "intro" env' typ'  in
                  bind uu____2973
                    (fun uu____2989  ->
                       match uu____2989 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3013 = set_solution goal sol  in
                           bind uu____3013
                             (fun uu____3019  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3021 =
                                  let uu____3024 = bnorm_goal g  in
                                  replace_cur uu____3024  in
                                bind uu____3021 (fun uu____3026  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3031 =
                 let uu____3032 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3033 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3032 uu____3033  in
               fail1 "goal is not an arrow (%s)" uu____3031)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2925
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3048  ->
    let uu____3055 = cur_goal ()  in
    bind uu____3055
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3072 =
            let uu____3079 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3079  in
          match uu____3072 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3092 =
                let uu____3093 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3093  in
              if uu____3092
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3106 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3106
                    in
                 let bs =
                   let uu____3116 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3116; b]  in
                 let env' =
                   let uu____3142 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3142 bs  in
                 let uu____3143 =
                   let uu____3150 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3150  in
                 bind uu____3143
                   (fun uu____3169  ->
                      match uu____3169 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3183 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3186 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3183
                              FStar_Parser_Const.effect_Tot_lid uu____3186 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3204 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3204 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3226 =
                                   let uu____3227 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3227.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3226
                                  in
                               let uu____3240 = set_solution goal tm  in
                               bind uu____3240
                                 (fun uu____3249  ->
                                    let uu____3250 =
                                      let uu____3253 =
                                        bnorm_goal
                                          (let uu___377_3256 = goal  in
                                           {
                                             FStar_Tactics_Types.goal_main_env
                                               =
                                               (uu___377_3256.FStar_Tactics_Types.goal_main_env);
                                             FStar_Tactics_Types.goal_ctx_uvar
                                               = ctx_uvar_u;
                                             FStar_Tactics_Types.opts =
                                               (uu___377_3256.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___377_3256.FStar_Tactics_Types.is_guard)
                                           })
                                         in
                                      replace_cur uu____3253  in
                                    bind uu____3250
                                      (fun uu____3263  ->
                                         let uu____3264 =
                                           let uu____3269 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3269, b)  in
                                         ret uu____3264)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3278 =
                let uu____3279 = FStar_Tactics_Types.goal_env goal  in
                let uu____3280 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3279 uu____3280  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3278))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3298 = cur_goal ()  in
    bind uu____3298
      (fun goal  ->
         mlog
           (fun uu____3305  ->
              let uu____3306 =
                let uu____3307 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3307  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3306)
           (fun uu____3312  ->
              let steps =
                let uu____3316 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu____3316
                 in
              let t =
                let uu____3320 = FStar_Tactics_Types.goal_env goal  in
                let uu____3321 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3320 uu____3321  in
              let uu____3322 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3322))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3346 =
          mlog
            (fun uu____3351  ->
               let uu____3352 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3352)
            (fun uu____3354  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3360 -> g.FStar_Tactics_Types.opts
                      | uu____3363 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3368  ->
                         let uu____3369 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3369)
                      (fun uu____3372  ->
                         let uu____3373 = __tc e t  in
                         bind uu____3373
                           (fun uu____3394  ->
                              match uu____3394 with
                              | (t1,uu____3404,uu____3405) ->
                                  let steps =
                                    let uu____3409 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Env.Reify;
                                      FStar_TypeChecker_Env.UnfoldTac]
                                      uu____3409
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3346
  
let (refine_intro : unit -> unit tac) =
  fun uu____3423  ->
    let uu____3426 =
      let uu____3429 = cur_goal ()  in
      bind uu____3429
        (fun g  ->
           let uu____3436 =
             let uu____3447 = FStar_Tactics_Types.goal_env g  in
             let uu____3448 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3447 uu____3448
              in
           match uu____3436 with
           | (uu____3451,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3476 =
                 let uu____3481 =
                   let uu____3486 =
                     let uu____3487 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3487]  in
                   FStar_Syntax_Subst.open_term uu____3486 phi  in
                 match uu____3481 with
                 | (bvs,phi1) ->
                     let uu____3512 =
                       let uu____3513 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3513  in
                     (uu____3512, phi1)
                  in
               (match uu____3476 with
                | (bv1,phi1) ->
                    let uu____3532 =
                      let uu____3535 = FStar_Tactics_Types.goal_env g  in
                      let uu____3536 =
                        let uu____3537 =
                          let uu____3540 =
                            let uu____3541 =
                              let uu____3548 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3548)  in
                            FStar_Syntax_Syntax.NT uu____3541  in
                          [uu____3540]  in
                        FStar_Syntax_Subst.subst uu____3537 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3535
                        uu____3536 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3532
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3556  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3426
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3575 = cur_goal ()  in
      bind uu____3575
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3583 = FStar_Tactics_Types.goal_env goal  in
               let uu____3584 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3583 uu____3584
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3586 = __tc env t  in
           bind uu____3586
             (fun uu____3605  ->
                match uu____3605 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3620  ->
                         let uu____3621 =
                           FStar_Syntax_Print.term_to_string typ  in
                         let uu____3622 =
                           let uu____3623 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3623
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3621 uu____3622)
                      (fun uu____3626  ->
                         let uu____3627 =
                           let uu____3630 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3630 guard  in
                         bind uu____3627
                           (fun uu____3632  ->
                              mlog
                                (fun uu____3636  ->
                                   let uu____3637 =
                                     FStar_Syntax_Print.term_to_string typ
                                      in
                                   let uu____3638 =
                                     let uu____3639 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     FStar_Syntax_Print.term_to_string
                                       uu____3639
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3637 uu____3638)
                                (fun uu____3642  ->
                                   let uu____3643 =
                                     let uu____3646 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3647 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3646 typ uu____3647  in
                                   bind uu____3643
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3653 =
                                             let uu____3654 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3654 t1  in
                                           let uu____3655 =
                                             let uu____3656 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3656 typ  in
                                           let uu____3657 =
                                             let uu____3658 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3659 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3658 uu____3659  in
                                           let uu____3660 =
                                             let uu____3661 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3662 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3661 uu____3662  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3653 uu____3655 uu____3657
                                             uu____3660)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3677 =
        mlog
          (fun uu____3682  ->
             let uu____3683 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3683)
          (fun uu____3686  ->
             let uu____3687 =
               let uu____3694 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3694  in
             bind uu____3687
               (fun uu___341_3703  ->
                  match uu___341_3703 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3713  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3716  ->
                           let uu____3717 =
                             let uu____3724 =
                               let uu____3727 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3727
                                 (fun uu____3732  ->
                                    let uu____3733 = refine_intro ()  in
                                    bind uu____3733
                                      (fun uu____3737  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3724  in
                           bind uu____3717
                             (fun uu___340_3744  ->
                                match uu___340_3744 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3752 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3677
  
let rec mapM : 'a 'b . ('a -> 'b tac) -> 'a Prims.list -> 'b Prims.list tac =
  fun f  ->
    fun l  ->
      match l with
      | [] -> ret []
      | x::xs ->
          let uu____3802 = f x  in
          bind uu____3802
            (fun y  ->
               let uu____3810 = mapM f xs  in
               bind uu____3810 (fun ys  -> ret (y :: ys)))
  
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
          let uu____3881 = do_unify e ty1 ty2  in
          bind uu____3881
            (fun uu___342_3893  ->
               if uu___342_3893
               then ret acc
               else
                 (let uu____3912 = FStar_Syntax_Util.arrow_one ty1  in
                  match uu____3912 with
                  | FStar_Pervasives_Native.None  ->
                      let uu____3933 = FStar_Syntax_Print.term_to_string ty1
                         in
                      let uu____3934 = FStar_Syntax_Print.term_to_string ty2
                         in
                      fail2 "Could not instantiate, %s to %s" uu____3933
                        uu____3934
                  | FStar_Pervasives_Native.Some (b,c) ->
                      let uu____3949 =
                        let uu____3950 = FStar_Syntax_Util.is_total_comp c
                           in
                        Prims.op_Negation uu____3950  in
                      if uu____3949
                      then fail "Codomain is effectful"
                      else
                        (let uu____3970 =
                           new_uvar "apply arg" e
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         bind uu____3970
                           (fun uu____3996  ->
                              match uu____3996 with
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
      let uu____4082 =
        mlog
          (fun uu____4087  ->
             let uu____4088 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4088)
          (fun uu____4091  ->
             let uu____4092 = cur_goal ()  in
             bind uu____4092
               (fun goal  ->
                  let e = FStar_Tactics_Types.goal_env goal  in
                  let uu____4100 = __tc e tm  in
                  bind uu____4100
                    (fun uu____4121  ->
                       match uu____4121 with
                       | (tm1,typ,guard) ->
                           let typ1 = bnorm e typ  in
                           let uu____4134 =
                             let uu____4145 =
                               FStar_Tactics_Types.goal_type goal  in
                             try_match_by_application e typ1 uu____4145  in
                           bind uu____4134
                             (fun uvs  ->
                                let w =
                                  FStar_List.fold_right
                                    (fun uu____4188  ->
                                       fun w  ->
                                         match uu____4188 with
                                         | (uvt,q,uu____4206) ->
                                             FStar_Syntax_Util.mk_app w
                                               [(uvt, q)]) uvs tm1
                                   in
                                let uvset =
                                  let uu____4238 =
                                    FStar_Syntax_Free.new_uv_set ()  in
                                  FStar_List.fold_right
                                    (fun uu____4255  ->
                                       fun s  ->
                                         match uu____4255 with
                                         | (uu____4267,uu____4268,uv) ->
                                             let uu____4270 =
                                               FStar_Syntax_Free.uvars
                                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                                in
                                             FStar_Util.set_union s
                                               uu____4270) uvs uu____4238
                                   in
                                let free_in_some_goal uv =
                                  FStar_Util.set_mem uv uvset  in
                                let uu____4279 = solve' goal w  in
                                bind uu____4279
                                  (fun uu____4284  ->
                                     let uu____4285 =
                                       mapM
                                         (fun uu____4302  ->
                                            match uu____4302 with
                                            | (uvt,q,uv) ->
                                                let uu____4314 =
                                                  FStar_Syntax_Unionfind.find
                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                   in
                                                (match uu____4314 with
                                                 | FStar_Pervasives_Native.Some
                                                     uu____4319 -> ret ()
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let uu____4320 =
                                                       uopt &&
                                                         (free_in_some_goal
                                                            uv)
                                                        in
                                                     if uu____4320
                                                     then ret ()
                                                     else
                                                       (let uu____4324 =
                                                          let uu____4327 =
                                                            bnorm_goal
                                                              (let uu___378_4330
                                                                 = goal  in
                                                               {
                                                                 FStar_Tactics_Types.goal_main_env
                                                                   =
                                                                   (uu___378_4330.FStar_Tactics_Types.goal_main_env);
                                                                 FStar_Tactics_Types.goal_ctx_uvar
                                                                   = uv;
                                                                 FStar_Tactics_Types.opts
                                                                   =
                                                                   (uu___378_4330.FStar_Tactics_Types.opts);
                                                                 FStar_Tactics_Types.is_guard
                                                                   = false
                                                               })
                                                             in
                                                          [uu____4327]  in
                                                        add_goals uu____4324)))
                                         uvs
                                        in
                                     bind uu____4285
                                       (fun uu____4334  ->
                                          proc_guard "apply guard" e guard))))))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4082
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4359 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4359
    then
      let uu____4366 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4381 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4434 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4366 with
      | (pre,post) ->
          let post1 =
            let uu____4466 =
              let uu____4477 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4477]  in
            FStar_Syntax_Util.mk_app post uu____4466  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4507 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4507
       then
         let uu____4514 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4514
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4547 =
      let uu____4550 =
        mlog
          (fun uu____4555  ->
             let uu____4556 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4556)
          (fun uu____4560  ->
             let is_unit_t t =
               let uu____4567 =
                 let uu____4568 = FStar_Syntax_Subst.compress t  in
                 uu____4568.FStar_Syntax_Syntax.n  in
               match uu____4567 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4572 -> false  in
             let uu____4573 = cur_goal ()  in
             bind uu____4573
               (fun goal  ->
                  let uu____4579 =
                    let uu____4588 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4588 tm  in
                  bind uu____4579
                    (fun uu____4603  ->
                       match uu____4603 with
                       | (tm1,t,guard) ->
                           let uu____4615 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4615 with
                            | (bs,comp) ->
                                let uu____4648 = lemma_or_sq comp  in
                                (match uu____4648 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4667 =
                                       FStar_List.fold_left
                                         (fun uu____4715  ->
                                            fun uu____4716  ->
                                              match (uu____4715, uu____4716)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4829 =
                                                    is_unit_t b_t  in
                                                  if uu____4829
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4867 =
                                                       let uu____4880 =
                                                         let uu____4881 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4881.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4884 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4880
                                                         uu____4884 b_t
                                                        in
                                                     match uu____4867 with
                                                     | (u,uu____4902,g_u) ->
                                                         let uu____4916 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4916,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4667 with
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
                                          let uu____4995 =
                                            let uu____4998 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4999 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____5000 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4998 uu____4999
                                              uu____5000
                                             in
                                          bind uu____4995
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____5008 =
                                                   let uu____5009 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____5009 tm1  in
                                                 let uu____5010 =
                                                   let uu____5011 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5012 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____5011 uu____5012
                                                    in
                                                 let uu____5013 =
                                                   let uu____5014 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____5015 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____5014 uu____5015
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____5008 uu____5010
                                                   uu____5013
                                               else
                                                 (let uu____5017 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____5017
                                                    (fun uu____5022  ->
                                                       let uu____5023 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____5023
                                                         (fun uu____5031  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____5056
                                                                  =
                                                                  let uu____5059
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____5059
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____5056
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
                                                                   let uu____5094
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____5094)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5110
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5110
                                                              with
                                                              | (hd1,uu____5128)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5154)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5171
                                                                    -> false)
                                                               in
                                                            let uu____5172 =
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
                                                                    let uu____5220
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    match uu____5220
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5248)
                                                                    ->
                                                                    let uu____5273
                                                                    =
                                                                    let uu____5274
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5274.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5273
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5288)
                                                                    ->
                                                                    let goal1
                                                                    =
                                                                    bnorm_goal
                                                                    (let uu___379_5308
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___379_5308.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___379_5308.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___379_5308.FStar_Tactics_Types.is_guard)
                                                                    })  in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5321
                                                                    ->
                                                                    let env =
                                                                    let uu___380_5323
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.dep_graph);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___380_5323.FStar_TypeChecker_Env.nbe)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5325
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5325
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
                                                                    let uu____5328
                                                                    =
                                                                    let uu____5335
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5335
                                                                    term1  in
                                                                    match uu____5328
                                                                    with
                                                                    | 
                                                                    (uu____5336,uu____5337,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5339
                                                                    =
                                                                    let uu____5344
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5344
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5339
                                                                    (fun
                                                                    uu___343_5356
                                                                     ->
                                                                    match uu___343_5356
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
                                                            bind uu____5172
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5424
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5424
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5446
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5446
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5507
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5507
                                                                    then
                                                                    let uu____5510
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5510
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
                                                                    let uu____5524
                                                                    =
                                                                    let uu____5525
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5525
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5524)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5526
                                                                   =
                                                                   let uu____5529
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5529
                                                                    guard
                                                                    in
                                                                 bind
                                                                   uu____5526
                                                                   (fun
                                                                    uu____5532
                                                                     ->
                                                                    let uu____5533
                                                                    =
                                                                    let uu____5536
                                                                    =
                                                                    let uu____5537
                                                                    =
                                                                    let uu____5538
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5539
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5538
                                                                    uu____5539
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5537
                                                                     in
                                                                    if
                                                                    uu____5536
                                                                    then
                                                                    let uu____5542
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5542
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5533
                                                                    (fun
                                                                    uu____5546
                                                                     ->
                                                                    let uu____5547
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5547
                                                                    (fun
                                                                    uu____5551
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4550  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4547
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5573 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5573 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5583::(e1,uu____5585)::(e2,uu____5587)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5648 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5672 = destruct_eq' typ  in
    match uu____5672 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5702 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5702 with
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
        let uu____5764 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5764 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5812 = aux e'  in
               FStar_Util.map_opt uu____5812
                 (fun uu____5836  ->
                    match uu____5836 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5857 = aux e  in
      FStar_Util.map_opt uu____5857
        (fun uu____5881  ->
           match uu____5881 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5948 =
            let uu____5957 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5957  in
          FStar_Util.map_opt uu____5948
            (fun uu____5972  ->
               match uu____5972 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___381_5991 = bv  in
                     let uu____5992 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___381_5991.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___381_5991.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5992
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___382_6000 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____6001 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____6010 =
                       let uu____6013 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____6013  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___382_6000.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____6001;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____6010;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___382_6000.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___382_6000.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___382_6000.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___383_6014 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___383_6014.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___383_6014.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___383_6014.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____6024 =
      let uu____6027 = cur_goal ()  in
      bind uu____6027
        (fun goal  ->
           let uu____6035 = h  in
           match uu____6035 with
           | (bv,uu____6039) ->
               mlog
                 (fun uu____6047  ->
                    let uu____6048 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____6049 =
                      FStar_Syntax_Print.term_to_string
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____6048
                      uu____6049)
                 (fun uu____6052  ->
                    let uu____6053 =
                      let uu____6062 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____6062  in
                    match uu____6053 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6083 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6083 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6098 =
                               let uu____6099 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6099.FStar_Syntax_Syntax.n  in
                             (match uu____6098 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___384_6116 = bv1  in
                                    let uu____6117 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___384_6116.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___384_6116.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6117
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___385_6125 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6126 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6135 =
                                      let uu____6138 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6138
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___385_6125.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6126;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6135;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___385_6125.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___385_6125.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___385_6125.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___386_6141 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___386_6141.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___386_6141.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___386_6141.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6142 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6143 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____6024
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6168 =
        let uu____6171 = cur_goal ()  in
        bind uu____6171
          (fun goal  ->
             let uu____6182 = b  in
             match uu____6182 with
             | (bv,uu____6186) ->
                 let bv' =
                   let uu____6192 =
                     let uu___387_6193 = bv  in
                     let uu____6194 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6194;
                       FStar_Syntax_Syntax.index =
                         (uu___387_6193.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___387_6193.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6192  in
                 let s1 =
                   let uu____6198 =
                     let uu____6199 =
                       let uu____6206 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6206)  in
                     FStar_Syntax_Syntax.NT uu____6199  in
                   [uu____6198]  in
                 let uu____6211 = subst_goal bv bv' s1 goal  in
                 (match uu____6211 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6168
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6230 =
      let uu____6233 = cur_goal ()  in
      bind uu____6233
        (fun goal  ->
           let uu____6242 = b  in
           match uu____6242 with
           | (bv,uu____6246) ->
               let uu____6251 =
                 let uu____6260 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6260  in
               (match uu____6251 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6281 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6281 with
                     | (ty,u) ->
                         let uu____6290 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6290
                           (fun uu____6308  ->
                              match uu____6308 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___388_6318 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___388_6318.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___388_6318.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6322 =
                                      let uu____6323 =
                                        let uu____6330 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6330)  in
                                      FStar_Syntax_Syntax.NT uu____6323  in
                                    [uu____6322]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___389_6342 = b1  in
                                         let uu____6343 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___389_6342.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___389_6342.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6343
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6350  ->
                                       let new_goal =
                                         let uu____6352 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6353 =
                                           let uu____6354 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6354
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6352 uu____6353
                                          in
                                       let uu____6355 = add_goals [new_goal]
                                          in
                                       bind uu____6355
                                         (fun uu____6360  ->
                                            let uu____6361 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6361
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6230
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6384 =
        let uu____6387 = cur_goal ()  in
        bind uu____6387
          (fun goal  ->
             let uu____6396 = b  in
             match uu____6396 with
             | (bv,uu____6400) ->
                 let uu____6405 =
                   let uu____6414 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6414  in
                 (match uu____6405 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6438 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Env.Reify;
                          FStar_TypeChecker_Env.UnfoldTac] uu____6438
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___390_6443 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___390_6443.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___390_6443.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6445 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6445))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6384
  
let (revert : unit -> unit tac) =
  fun uu____6456  ->
    let uu____6459 = cur_goal ()  in
    bind uu____6459
      (fun goal  ->
         let uu____6465 =
           let uu____6472 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6472  in
         match uu____6465 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6488 =
                 let uu____6491 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6491  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6488
                in
             let uu____6506 = new_uvar "revert" env' typ'  in
             bind uu____6506
               (fun uu____6521  ->
                  match uu____6521 with
                  | (r,u_r) ->
                      let uu____6530 =
                        let uu____6533 =
                          let uu____6534 =
                            let uu____6535 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6535.FStar_Syntax_Syntax.pos  in
                          let uu____6538 =
                            let uu____6543 =
                              let uu____6544 =
                                let uu____6553 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6553  in
                              [uu____6544]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6543  in
                          uu____6538 FStar_Pervasives_Native.None uu____6534
                           in
                        set_solution goal uu____6533  in
                      bind uu____6530
                        (fun uu____6574  ->
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
      let uu____6586 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6586
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6601 = cur_goal ()  in
    bind uu____6601
      (fun goal  ->
         mlog
           (fun uu____6609  ->
              let uu____6610 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6611 =
                let uu____6612 =
                  let uu____6613 =
                    let uu____6622 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6622  in
                  FStar_All.pipe_right uu____6613 FStar_List.length  in
                FStar_All.pipe_right uu____6612 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6610 uu____6611)
           (fun uu____6639  ->
              let uu____6640 =
                let uu____6649 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6649  in
              match uu____6640 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6688 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6688
                        then
                          let uu____6691 =
                            let uu____6692 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6692
                             in
                          fail uu____6691
                        else check1 bvs2
                     in
                  let uu____6694 =
                    let uu____6695 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6695  in
                  if uu____6694
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6699 = check1 bvs  in
                     bind uu____6699
                       (fun uu____6705  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6707 =
                            let uu____6714 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6714  in
                          bind uu____6707
                            (fun uu____6723  ->
                               match uu____6723 with
                               | (ut,uvar_ut) ->
                                   let uu____6732 = set_solution goal ut  in
                                   bind uu____6732
                                     (fun uu____6737  ->
                                        let uu____6738 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6738))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6745  ->
    let uu____6748 = cur_goal ()  in
    bind uu____6748
      (fun goal  ->
         let uu____6754 =
           let uu____6761 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6761  in
         match uu____6754 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6769) ->
             let uu____6774 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6774)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6784 = cur_goal ()  in
    bind uu____6784
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6794 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6794  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6797  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6807 = cur_goal ()  in
    bind uu____6807
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6817 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6817  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6820  -> add_goals [g']))
  
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
            let uu____6860 = FStar_Syntax_Subst.compress t  in
            uu____6860.FStar_Syntax_Syntax.n  in
          let uu____6863 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___394_6869 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___394_6869.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___394_6869.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6863
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6885 =
                   let uu____6886 = FStar_Syntax_Subst.compress t1  in
                   uu____6886.FStar_Syntax_Syntax.n  in
                 match uu____6885 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6917 = ff hd1  in
                     bind uu____6917
                       (fun hd2  ->
                          let fa uu____6943 =
                            match uu____6943 with
                            | (a,q) ->
                                let uu____6964 = ff a  in
                                bind uu____6964 (fun a1  -> ret (a1, q))
                             in
                          let uu____6983 = mapM fa args  in
                          bind uu____6983
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____7065 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____7065 with
                      | (bs1,t') ->
                          let uu____7074 =
                            let uu____7077 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____7077 t'  in
                          bind uu____7074
                            (fun t''  ->
                               let uu____7081 =
                                 let uu____7082 =
                                   let uu____7101 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____7110 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____7101, uu____7110, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____7082  in
                               ret uu____7081))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7185 = ff hd1  in
                     bind uu____7185
                       (fun hd2  ->
                          let ffb br =
                            let uu____7200 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7200 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7232 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7232  in
                                let uu____7233 = ff1 e  in
                                bind uu____7233
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7248 = mapM ffb brs  in
                          bind uu____7248
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7292;
                          FStar_Syntax_Syntax.lbtyp = uu____7293;
                          FStar_Syntax_Syntax.lbeff = uu____7294;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7296;
                          FStar_Syntax_Syntax.lbpos = uu____7297;_}::[]),e)
                     ->
                     let lb =
                       let uu____7322 =
                         let uu____7323 = FStar_Syntax_Subst.compress t1  in
                         uu____7323.FStar_Syntax_Syntax.n  in
                       match uu____7322 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7327) -> lb
                       | uu____7340 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7349 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7349
                         (fun def1  ->
                            ret
                              (let uu___391_7355 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___391_7355.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___391_7355.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___391_7355.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___391_7355.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___391_7355.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___391_7355.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7356 = fflb lb  in
                     bind uu____7356
                       (fun lb1  ->
                          let uu____7366 =
                            let uu____7371 =
                              let uu____7372 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7372]  in
                            FStar_Syntax_Subst.open_term uu____7371 e  in
                          match uu____7366 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7402 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7402  in
                              let uu____7403 = ff1 e1  in
                              bind uu____7403
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7444 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7444
                         (fun def  ->
                            ret
                              (let uu___392_7450 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___392_7450.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___392_7450.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___392_7450.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___392_7450.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___392_7450.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___392_7450.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7451 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7451 with
                      | (lbs1,e1) ->
                          let uu____7466 = mapM fflb lbs1  in
                          bind uu____7466
                            (fun lbs2  ->
                               let uu____7478 = ff e1  in
                               bind uu____7478
                                 (fun e2  ->
                                    let uu____7486 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7486 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7554 = ff t2  in
                     bind uu____7554
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7585 = ff t2  in
                     bind uu____7585
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7592 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___393_7599 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___393_7599.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___393_7599.FStar_Syntax_Syntax.vars)
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
            let uu____7636 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7636 with
            | (t1,lcomp,g) ->
                let uu____7648 =
                  (let uu____7651 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7651) ||
                    (let uu____7653 = FStar_TypeChecker_Env.is_trivial g  in
                     Prims.op_Negation uu____7653)
                   in
                if uu____7648
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7661 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7661
                       (fun uu____7677  ->
                          match uu____7677 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7690  ->
                                    let uu____7691 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7692 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7691 uu____7692);
                               (let uu____7693 =
                                  let uu____7696 =
                                    let uu____7697 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7697 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7696
                                    opts
                                   in
                                bind uu____7693
                                  (fun uu____7700  ->
                                     let uu____7701 =
                                       bind tau
                                         (fun uu____7707  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7713  ->
                                                 let uu____7714 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7715 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7714 uu____7715);
                                            ret ut1)
                                        in
                                     focus uu____7701))))
                      in
                   let uu____7716 = trytac' rewrite_eq  in
                   bind uu____7716
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
          let uu____7914 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7914
            (fun t1  ->
               let uu____7922 =
                 f env
                   (let uu___397_7931 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___397_7931.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___397_7931.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7922
                 (fun uu____7947  ->
                    match uu____7947 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7970 =
                               let uu____7971 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7971.FStar_Syntax_Syntax.n  in
                             match uu____7970 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____8008 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____8008
                                   (fun uu____8033  ->
                                      match uu____8033 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____8049 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____8049
                                            (fun uu____8076  ->
                                               match uu____8076 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___395_8106 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___395_8106.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___395_8106.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____8148 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____8148 with
                                  | (bs1,t') ->
                                      let uu____8163 =
                                        let uu____8170 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____8170 ctrl1 t'
                                         in
                                      bind uu____8163
                                        (fun uu____8188  ->
                                           match uu____8188 with
                                           | (t'',ctrl2) ->
                                               let uu____8203 =
                                                 let uu____8210 =
                                                   let uu___396_8213 = t4  in
                                                   let uu____8216 =
                                                     let uu____8217 =
                                                       let uu____8236 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8245 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8236,
                                                         uu____8245, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8217
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8216;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___396_8213.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___396_8213.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8210, ctrl2)  in
                                               ret uu____8203))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8298 -> ret (t3, ctrl1))))

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
              let uu____8345 = ctrl_tac_fold f env ctrl t  in
              bind uu____8345
                (fun uu____8369  ->
                   match uu____8369 with
                   | (t1,ctrl1) ->
                       let uu____8384 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8384
                         (fun uu____8411  ->
                            match uu____8411 with
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
              let uu____8495 =
                let uu____8502 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8502
                  (fun uu____8511  ->
                     let uu____8512 = ctrl t1  in
                     bind uu____8512
                       (fun res  ->
                          let uu____8535 = trivial ()  in
                          bind uu____8535 (fun uu____8543  -> ret res)))
                 in
              bind uu____8495
                (fun uu____8559  ->
                   match uu____8559 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8583 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8583 with
                          | (t2,lcomp,g) ->
                              let uu____8599 =
                                (let uu____8602 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8602) ||
                                  (let uu____8604 =
                                     FStar_TypeChecker_Env.is_trivial g  in
                                   Prims.op_Negation uu____8604)
                                 in
                              if uu____8599
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8617 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8617
                                   (fun uu____8637  ->
                                      match uu____8637 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8654  ->
                                                let uu____8655 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8656 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8655 uu____8656);
                                           (let uu____8657 =
                                              let uu____8660 =
                                                let uu____8661 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8661 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8660 opts
                                               in
                                            bind uu____8657
                                              (fun uu____8668  ->
                                                 let uu____8669 =
                                                   bind rewriter
                                                     (fun uu____8683  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8689  ->
                                                             let uu____8690 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8691 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8690
                                                               uu____8691);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8669)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8732 =
        bind get
          (fun ps  ->
             let uu____8742 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8742 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8779  ->
                       let uu____8780 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8780);
                  bind dismiss_all
                    (fun uu____8783  ->
                       let uu____8784 =
                         let uu____8791 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8791
                           keepGoing gt1
                          in
                       bind uu____8784
                         (fun uu____8803  ->
                            match uu____8803 with
                            | (gt',uu____8811) ->
                                (log ps
                                   (fun uu____8815  ->
                                      let uu____8816 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8816);
                                 (let uu____8817 = push_goals gs  in
                                  bind uu____8817
                                    (fun uu____8822  ->
                                       let uu____8823 =
                                         let uu____8826 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8826]  in
                                       add_goals uu____8823)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8732
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8849 =
        bind get
          (fun ps  ->
             let uu____8859 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8859 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8896  ->
                       let uu____8897 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8897);
                  bind dismiss_all
                    (fun uu____8900  ->
                       let uu____8901 =
                         let uu____8904 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8904 gt1
                          in
                       bind uu____8901
                         (fun gt'  ->
                            log ps
                              (fun uu____8912  ->
                                 let uu____8913 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8913);
                            (let uu____8914 = push_goals gs  in
                             bind uu____8914
                               (fun uu____8919  ->
                                  let uu____8920 =
                                    let uu____8923 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8923]  in
                                  add_goals uu____8920))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8849
  
let (trefl : unit -> unit tac) =
  fun uu____8934  ->
    let uu____8937 =
      let uu____8940 = cur_goal ()  in
      bind uu____8940
        (fun g  ->
           let uu____8958 =
             let uu____8963 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8963  in
           match uu____8958 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8971 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8971 with
                | (hd1,args) ->
                    let uu____9010 =
                      let uu____9023 =
                        let uu____9024 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____9024.FStar_Syntax_Syntax.n  in
                      (uu____9023, args)  in
                    (match uu____9010 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____9038::(l,uu____9040)::(r,uu____9042)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____9089 =
                           let uu____9092 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____9092 l r  in
                         bind uu____9089
                           (fun b  ->
                              if b
                              then solve' g FStar_Syntax_Util.exp_unit
                              else
                                (let l1 =
                                   let uu____9099 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9099 l
                                    in
                                 let r1 =
                                   let uu____9101 =
                                     FStar_Tactics_Types.goal_env g  in
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.UnfoldUntil
                                        FStar_Syntax_Syntax.delta_constant;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.UnfoldTac]
                                     uu____9101 r
                                    in
                                 let uu____9102 =
                                   let uu____9105 =
                                     FStar_Tactics_Types.goal_env g  in
                                   do_unify uu____9105 l1 r1  in
                                 bind uu____9102
                                   (fun b1  ->
                                      if b1
                                      then
                                        solve' g FStar_Syntax_Util.exp_unit
                                      else
                                        (let uu____9111 =
                                           let uu____9112 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9112 l1  in
                                         let uu____9113 =
                                           let uu____9114 =
                                             FStar_Tactics_Types.goal_env g
                                              in
                                           tts uu____9114 r1  in
                                         fail2
                                           "not a trivial equality ((%s) vs (%s))"
                                           uu____9111 uu____9113))))
                     | (hd2,uu____9116) ->
                         let uu____9133 =
                           let uu____9134 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____9134 t  in
                         fail1 "trefl: not an equality (%s)" uu____9133))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8937
  
let (dup : unit -> unit tac) =
  fun uu____9147  ->
    let uu____9150 = cur_goal ()  in
    bind uu____9150
      (fun g  ->
         let uu____9156 =
           let uu____9163 = FStar_Tactics_Types.goal_env g  in
           let uu____9164 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____9163 uu____9164  in
         bind uu____9156
           (fun uu____9173  ->
              match uu____9173 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___398_9183 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___398_9183.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___398_9183.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___398_9183.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____9186  ->
                       let uu____9187 =
                         let uu____9190 = FStar_Tactics_Types.goal_env g  in
                         let uu____9191 =
                           let uu____9192 =
                             let uu____9193 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____9194 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____9193
                               uu____9194
                              in
                           let uu____9195 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____9196 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____9192 uu____9195 u
                             uu____9196
                            in
                         add_irrelevant_goal "dup equation" uu____9190
                           uu____9191 g.FStar_Tactics_Types.opts
                          in
                       bind uu____9187
                         (fun uu____9199  ->
                            let uu____9200 = add_goals [g']  in
                            bind uu____9200 (fun uu____9204  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____9211  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___399_9228 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___399_9228.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___399_9228.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___399_9228.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___399_9228.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___399_9228.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___399_9228.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___399_9228.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___399_9228.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___399_9228.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___399_9228.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___399_9228.FStar_Tactics_Types.tac_verb_dbg)
                })
         | uu____9229 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____9238  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___400_9251 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___400_9251.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___400_9251.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___400_9251.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___400_9251.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___400_9251.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___400_9251.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___400_9251.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___400_9251.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___400_9251.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___400_9251.FStar_Tactics_Types.freshness);
                  FStar_Tactics_Types.tac_verb_dbg =
                    (uu___400_9251.FStar_Tactics_Types.tac_verb_dbg)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9258  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9265 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9285 =
      let uu____9292 = cur_goal ()  in
      bind uu____9292
        (fun g  ->
           let uu____9302 =
             let uu____9311 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9311 t  in
           bind uu____9302
             (fun uu____9339  ->
                match uu____9339 with
                | (t1,typ,guard) ->
                    let uu____9355 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9355 with
                     | (hd1,args) ->
                         let uu____9404 =
                           let uu____9419 =
                             let uu____9420 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9420.FStar_Syntax_Syntax.n  in
                           (uu____9419, args)  in
                         (match uu____9404 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9441)::(q,uu____9443)::[]) when
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
                                let uu____9497 =
                                  let uu____9498 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9498
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9497
                                 in
                              let g2 =
                                let uu____9500 =
                                  let uu____9501 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9501
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9500
                                 in
                              bind __dismiss
                                (fun uu____9508  ->
                                   let uu____9509 = add_goals [g1; g2]  in
                                   bind uu____9509
                                     (fun uu____9518  ->
                                        let uu____9519 =
                                          let uu____9524 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9525 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9524, uu____9525)  in
                                        ret uu____9519))
                          | uu____9530 ->
                              let uu____9545 =
                                let uu____9546 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9546 typ  in
                              fail1 "Not a disjunction: %s" uu____9545))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9285
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9576 =
      let uu____9579 = cur_goal ()  in
      bind uu____9579
        (fun g  ->
           FStar_Options.push ();
           (let uu____9592 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9592);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___401_9599 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___401_9599.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___401_9599.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___401_9599.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9576
  
let (top_env : unit -> env tac) =
  fun uu____9611  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9624  ->
    let uu____9627 = cur_goal ()  in
    bind uu____9627
      (fun g  ->
         let uu____9633 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9633)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9642  ->
    let uu____9645 = cur_goal ()  in
    bind uu____9645
      (fun g  ->
         let uu____9651 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9651)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9660  ->
    let uu____9663 = cur_goal ()  in
    bind uu____9663
      (fun g  ->
         let uu____9669 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9669)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9686 =
        mlog
          (fun uu____9691  ->
             let uu____9692 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "unquote: tm = %s\n" uu____9692)
          (fun uu____9695  ->
             let uu____9696 = cur_goal ()  in
             bind uu____9696
               (fun goal  ->
                  let env =
                    let uu____9704 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.set_expected_typ uu____9704 ty  in
                  let uu____9705 = __tc env tm  in
                  bind uu____9705
                    (fun uu____9724  ->
                       match uu____9724 with
                       | (tm1,typ,guard) ->
                           mlog
                             (fun uu____9738  ->
                                let uu____9739 =
                                  FStar_Syntax_Print.term_to_string tm1  in
                                FStar_Util.print1 "unquote: tm' = %s\n"
                                  uu____9739)
                             (fun uu____9741  ->
                                mlog
                                  (fun uu____9744  ->
                                     let uu____9745 =
                                       FStar_Syntax_Print.term_to_string typ
                                        in
                                     FStar_Util.print1 "unquote: typ = %s\n"
                                       uu____9745)
                                  (fun uu____9748  ->
                                     let uu____9749 =
                                       proc_guard "unquote" env guard  in
                                     bind uu____9749
                                       (fun uu____9753  -> ret tm1))))))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9686
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9776 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9782 =
              let uu____9789 =
                let uu____9790 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9790
                 in
              new_uvar "uvar_env.2" env uu____9789  in
            bind uu____9782
              (fun uu____9806  ->
                 match uu____9806 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9776
        (fun typ  ->
           let uu____9818 = new_uvar "uvar_env" env typ  in
           bind uu____9818
             (fun uu____9832  -> match uu____9832 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9850 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9869 -> g.FStar_Tactics_Types.opts
             | uu____9872 -> FStar_Options.peek ()  in
           let uu____9875 = FStar_Syntax_Util.head_and_args t  in
           match uu____9875 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9895);
                FStar_Syntax_Syntax.pos = uu____9896;
                FStar_Syntax_Syntax.vars = uu____9897;_},uu____9898)
               ->
               let env1 =
                 let uu___402_9940 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___402_9940.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___402_9940.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___402_9940.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___402_9940.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___402_9940.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___402_9940.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___402_9940.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___402_9940.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___402_9940.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___402_9940.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___402_9940.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___402_9940.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___402_9940.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___402_9940.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___402_9940.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___402_9940.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___402_9940.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___402_9940.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___402_9940.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___402_9940.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___402_9940.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___402_9940.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___402_9940.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___402_9940.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___402_9940.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___402_9940.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___402_9940.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___402_9940.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___402_9940.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___402_9940.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___402_9940.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___402_9940.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___402_9940.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___402_9940.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___402_9940.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___402_9940.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___402_9940.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___402_9940.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___402_9940.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___402_9940.FStar_TypeChecker_Env.dep_graph);
                   FStar_TypeChecker_Env.nbe =
                     (uu___402_9940.FStar_TypeChecker_Env.nbe)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let uu____9942 =
                 let uu____9945 = bnorm_goal g  in [uu____9945]  in
               add_goals uu____9942
           | uu____9946 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9850
  
let (tac_and : Prims.bool tac -> Prims.bool tac -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      let comp =
        bind t1
          (fun b  ->
             let uu____9995 = if b then t2 else ret false  in
             bind uu____9995 (fun b'  -> if b' then ret b' else fail ""))
         in
      let uu____10006 = trytac comp  in
      bind uu____10006
        (fun uu___344_10014  ->
           match uu___344_10014 with
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
        let uu____10040 =
          bind get
            (fun ps  ->
               let uu____10046 = __tc e t1  in
               bind uu____10046
                 (fun uu____10066  ->
                    match uu____10066 with
                    | (t11,ty1,g1) ->
                        let uu____10078 = __tc e t2  in
                        bind uu____10078
                          (fun uu____10098  ->
                             match uu____10098 with
                             | (t21,ty2,g2) ->
                                 let uu____10110 =
                                   proc_guard "unify_env g1" e g1  in
                                 bind uu____10110
                                   (fun uu____10115  ->
                                      let uu____10116 =
                                        proc_guard "unify_env g2" e g2  in
                                      bind uu____10116
                                        (fun uu____10122  ->
                                           let uu____10123 =
                                             do_unify e ty1 ty2  in
                                           let uu____10126 =
                                             do_unify e t11 t21  in
                                           tac_and uu____10123 uu____10126)))))
           in
        FStar_All.pipe_left (wrap_err "unify_env") uu____10040
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____10159  ->
             let uu____10160 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____10160
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
        (fun uu____10181  ->
           let uu____10182 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____10182)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____10192 =
      mlog
        (fun uu____10197  ->
           let uu____10198 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____10198)
        (fun uu____10201  ->
           let uu____10202 = cur_goal ()  in
           bind uu____10202
             (fun g  ->
                let uu____10208 =
                  let uu____10217 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____10217 ty  in
                bind uu____10208
                  (fun uu____10229  ->
                     match uu____10229 with
                     | (ty1,uu____10239,guard) ->
                         let uu____10241 =
                           let uu____10244 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____10244 guard  in
                         bind uu____10241
                           (fun uu____10247  ->
                              let uu____10248 =
                                let uu____10251 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____10252 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____10251 uu____10252 ty1  in
                              bind uu____10248
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____10258 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____10258
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
                                        let uu____10264 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____10265 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____10264
                                          uu____10265
                                         in
                                      let nty =
                                        let uu____10267 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____10267 ty1  in
                                      let uu____10268 =
                                        let uu____10271 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____10271 ng nty  in
                                      bind uu____10268
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____10277 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____10277
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____10192
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____10299::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____10327 = init xs  in x :: uu____10327
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____10339 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____10347) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____10412 = last args  in
          (match uu____10412 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____10442 =
                 let uu____10443 =
                   let uu____10448 =
                     let uu____10449 =
                       let uu____10454 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____10454  in
                     uu____10449 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____10448, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____10443  in
               FStar_All.pipe_left ret uu____10442)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10467,uu____10468) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10520 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10520 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10561 =
                      let uu____10562 =
                        let uu____10567 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10567)  in
                      FStar_Reflection_Data.Tv_Abs uu____10562  in
                    FStar_All.pipe_left ret uu____10561))
      | FStar_Syntax_Syntax.Tm_type uu____10570 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10594 ->
          let uu____10609 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10609 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10639 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10639 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10692 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10704 =
            let uu____10705 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10705  in
          FStar_All.pipe_left ret uu____10704
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10726 =
            let uu____10727 =
              let uu____10732 =
                let uu____10733 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10733  in
              (uu____10732, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10727  in
          FStar_All.pipe_left ret uu____10726
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10767 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10772 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10772 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10825 ->
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
             | FStar_Util.Inr uu____10859 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10863 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10863 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10883 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10887 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10941 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10941
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10960 =
                  let uu____10967 =
                    FStar_List.map
                      (fun uu____10979  ->
                         match uu____10979 with
                         | (p1,uu____10987) -> inspect_pat p1) ps
                     in
                  (fv, uu____10967)  in
                FStar_Reflection_Data.Pat_Cons uu____10960
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
              (fun uu___345_11081  ->
                 match uu___345_11081 with
                 | (pat,uu____11103,t4) ->
                     let uu____11121 = inspect_pat pat  in (uu____11121, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____11130 ->
          ((let uu____11132 =
              let uu____11137 =
                let uu____11138 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____11139 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____11138 uu____11139
                 in
              (FStar_Errors.Warning_CantInspect, uu____11137)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____11132);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____10339
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____11152 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____11152
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____11156 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____11156
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____11160 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____11160
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____11167 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____11167
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____11192 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____11192
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____11209 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____11209
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____11228 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____11228
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____11232 =
          let uu____11233 =
            let uu____11240 =
              let uu____11241 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____11241  in
            FStar_Syntax_Syntax.mk uu____11240  in
          uu____11233 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____11232
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____11249 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11249
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____11258 =
          let uu____11259 =
            let uu____11266 =
              let uu____11267 =
                let uu____11280 =
                  let uu____11283 =
                    let uu____11284 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____11284]  in
                  FStar_Syntax_Subst.close uu____11283 t2  in
                ((false, [lb]), uu____11280)  in
              FStar_Syntax_Syntax.Tm_let uu____11267  in
            FStar_Syntax_Syntax.mk uu____11266  in
          uu____11259 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____11258
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____11324 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____11324 with
         | (lbs,body) ->
             let uu____11339 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____11339)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____11373 =
                let uu____11374 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____11374  in
              FStar_All.pipe_left wrap uu____11373
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____11381 =
                let uu____11382 =
                  let uu____11395 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____11411 = pack_pat p1  in
                         (uu____11411, false)) ps
                     in
                  (fv, uu____11395)  in
                FStar_Syntax_Syntax.Pat_cons uu____11382  in
              FStar_All.pipe_left wrap uu____11381
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
            (fun uu___346_11457  ->
               match uu___346_11457 with
               | (pat,t1) ->
                   let uu____11474 = pack_pat pat  in
                   (uu____11474, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____11522 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11522
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11550 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11550
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11596 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11596
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11635 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11635
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11656 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11656 with
      | (u,ctx_uvars,g_u) ->
          let uu____11688 = FStar_List.hd ctx_uvars  in
          (match uu____11688 with
           | (ctx_uvar,uu____11702) ->
               let g =
                 let uu____11704 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11704 false
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
        let uu____11724 = goal_of_goal_ty env typ  in
        match uu____11724 with
        | (g,g_u) ->
            let ps =
              let uu____11736 =
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
                FStar_Tactics_Types.tac_verb_dbg = uu____11736
              }  in
            let uu____11741 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11741)
  