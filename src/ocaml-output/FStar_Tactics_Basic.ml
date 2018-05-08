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
          let uu____160 =
            let uu____165 = FStar_Util.message_of_exn e  in (uu____165, p)
             in
          FStar_Tactics_Result.Failed uu____160
  
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____221 = run t1 p  in
           match uu____221 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____228 = t2 a  in run uu____228 q
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
    let uu____248 =
      FStar_Syntax_Unionfind.find uv.FStar_Syntax_Syntax.ctx_uvar_head  in
    match uu____248 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (check_goal_solved :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun goal  -> get_uvar_solved goal.FStar_Tactics_Types.goal_ctx_uvar 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let uu____266 =
      FStar_Syntax_Print.ctx_uvar_to_string
        g.FStar_Tactics_Types.goal_ctx_uvar
       in
    let uu____267 =
      let uu____268 = check_goal_solved g  in
      match uu____268 with
      | FStar_Pervasives_Native.None  -> ""
      | FStar_Pervasives_Native.Some t ->
          let uu____272 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.format1 "\tGOAL ALREADY SOLVED!: %s" uu____272
       in
    FStar_Util.format2 "%s%s" uu____266 uu____267
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____288 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____288
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____304 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____304
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____325 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____325
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____332) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____342) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____357 =
      let uu____362 =
        let uu____363 = FStar_Tactics_Types.goal_env g  in
        let uu____364 = FStar_Tactics_Types.goal_type g  in
        FStar_TypeChecker_Normalize.unfold_whnf uu____363 uu____364  in
      FStar_Syntax_Util.un_squash uu____362  in
    match uu____357 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____370 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____398 =
            let uu____399 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____399  in
          if uu____398 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____407 . 'Auu____407 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____419 = goal_to_string goal  in tacprint uu____419
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____431 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____435 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____435))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____444  ->
    match uu____444 with
    | (msg,ps) ->
        let uu____451 =
          let uu____454 =
            let uu____455 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____455 msg
             in
          let uu____456 =
            let uu____459 =
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____460 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____460
              else ""  in
            let uu____462 =
              let uu____465 =
                let uu____466 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____467 =
                  let uu____468 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____468  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____466
                  uu____467
                 in
              let uu____471 =
                let uu____474 =
                  let uu____475 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____476 =
                    let uu____477 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____477  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____475
                    uu____476
                   in
                [uu____474]  in
              uu____465 :: uu____471  in
            uu____459 :: uu____462  in
          uu____454 :: uu____456  in
        FStar_String.concat "" uu____451
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____486 =
        let uu____487 = FStar_Tactics_Types.goal_env g  in
        FStar_TypeChecker_Env.all_binders uu____487  in
      let uu____488 =
        let uu____493 =
          let uu____494 = FStar_Tactics_Types.goal_env g  in
          FStar_TypeChecker_Env.dsenv uu____494  in
        FStar_Syntax_Print.binders_to_json uu____493  in
      FStar_All.pipe_right uu____486 uu____488  in
    let uu____495 =
      let uu____502 =
        let uu____509 =
          let uu____514 =
            let uu____515 =
              let uu____522 =
                let uu____527 =
                  let uu____528 =
                    let uu____529 = FStar_Tactics_Types.goal_env g  in
                    let uu____530 = FStar_Tactics_Types.goal_witness g  in
                    tts uu____529 uu____530  in
                  FStar_Util.JsonStr uu____528  in
                ("witness", uu____527)  in
              let uu____531 =
                let uu____538 =
                  let uu____543 =
                    let uu____544 =
                      let uu____545 = FStar_Tactics_Types.goal_env g  in
                      let uu____546 = FStar_Tactics_Types.goal_type g  in
                      tts uu____545 uu____546  in
                    FStar_Util.JsonStr uu____544  in
                  ("type", uu____543)  in
                [uu____538]  in
              uu____522 :: uu____531  in
            FStar_Util.JsonAssoc uu____515  in
          ("goal", uu____514)  in
        [uu____509]  in
      ("hyps", g_binders) :: uu____502  in
    FStar_Util.JsonAssoc uu____495
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____579  ->
    match uu____579 with
    | (msg,ps) ->
        let uu____586 =
          let uu____593 =
            let uu____600 =
              let uu____607 =
                let uu____614 =
                  let uu____619 =
                    let uu____620 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____620  in
                  ("goals", uu____619)  in
                let uu____623 =
                  let uu____630 =
                    let uu____635 =
                      let uu____636 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____636  in
                    ("smt-goals", uu____635)  in
                  [uu____630]  in
                uu____614 :: uu____623  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____607
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____600  in
          let uu____659 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____672 =
                let uu____677 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____677)  in
              [uu____672]
            else []  in
          FStar_List.append uu____593 uu____659  in
        FStar_Util.JsonAssoc uu____586
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____707  ->
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
         (let uu____730 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____730 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____748 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____748 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____781 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____781 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____812 =
              let uu____815 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____815  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____812);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____896 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____896
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____904 . Prims.string -> Prims.string -> 'Auu____904 tac =
  fun msg  ->
    fun x  -> let uu____917 = FStar_Util.format1 msg x  in fail uu____917
  
let fail2 :
  'Auu____926 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____926 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____944 = FStar_Util.format2 msg x y  in fail uu____944
  
let fail3 :
  'Auu____955 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____955 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____978 = FStar_Util.format3 msg x y z  in fail uu____978
  
let fail4 :
  'Auu____991 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____991 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____1019 = FStar_Util.format4 msg x y z w  in
            fail uu____1019
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1052 = run t ps  in
         match uu____1052 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___96_1076 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___96_1076.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___96_1076.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___96_1076.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___96_1076.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___96_1076.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___96_1076.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___96_1076.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___96_1076.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___96_1076.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___96_1076.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1103 = trytac' t  in
    bind uu____1103
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1130 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1166 = trytac t  in run uu____1166 ps
         with
         | FStar_Errors.Err (uu____1182,msg) ->
             (log ps
                (fun uu____1186  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1191,msg,uu____1193) ->
             (log ps
                (fun uu____1196  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1229 = run t ps  in
           match uu____1229 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1248  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1269 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1269
         then
           let uu____1270 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1271 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1270
             uu____1271
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1283 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1283
            then
              let uu____1284 = FStar_Util.string_of_bool res  in
              let uu____1285 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1286 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1284 uu____1285 uu____1286
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1294,msg) ->
             mlog
               (fun uu____1297  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1299  -> ret false)
         | FStar_Errors.Error (uu____1300,msg,r) ->
             mlog
               (fun uu____1305  ->
                  let uu____1306 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1306) (fun uu____1308  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1331  ->
             (let uu____1333 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1333
              then
                (FStar_Options.push ();
                 (let uu____1335 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1337 =
                let uu____1340 = __do_unify env t1 t2  in
                bind uu____1340
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
              bind uu____1337
                (fun r  ->
                   (let uu____1356 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1356 then FStar_Options.pop () else ());
                   ret r)))
  
let (remove_solved_goals : unit tac) =
  bind get
    (fun ps  ->
       let ps' =
         let uu___101_1364 = ps  in
         let uu____1365 =
           FStar_List.filter
             (fun g  ->
                let uu____1371 = check_goal_solved g  in
                FStar_Option.isNone uu____1371) ps.FStar_Tactics_Types.goals
            in
         {
           FStar_Tactics_Types.main_context =
             (uu___101_1364.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___101_1364.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___101_1364.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1365;
           FStar_Tactics_Types.smt_goals =
             (uu___101_1364.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___101_1364.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___101_1364.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___101_1364.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___101_1364.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___101_1364.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___101_1364.FStar_Tactics_Types.freshness)
         }  in
       set ps')
  
let (set_solution :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1388 =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
         in
      match uu____1388 with
      | FStar_Pervasives_Native.Some uu____1393 ->
          let uu____1394 =
            let uu____1395 = goal_to_string goal  in
            FStar_Util.format1 "Goal %s is already solved" uu____1395  in
          fail uu____1394
      | FStar_Pervasives_Native.None  ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           ret ())
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      let uu____1411 = FStar_Tactics_Types.goal_env goal  in
      let uu____1412 = FStar_Tactics_Types.goal_witness goal  in
      do_unify uu____1411 solution uu____1412
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1418 =
         let uu___102_1419 = p  in
         let uu____1420 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___102_1419.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___102_1419.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___102_1419.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1420;
           FStar_Tactics_Types.smt_goals =
             (uu___102_1419.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___102_1419.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___102_1419.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___102_1419.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___102_1419.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___102_1419.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___102_1419.FStar_Tactics_Types.freshness)
         }  in
       set uu____1418)
  
let (dismiss : unit -> unit tac) =
  fun uu____1429  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1436 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = FStar_Tactics_Types.goal_env goal  in
      mlog
        (fun uu____1457  ->
           let uu____1458 =
             let uu____1459 = FStar_Tactics_Types.goal_witness goal  in
             tts e uu____1459  in
           let uu____1460 = tts e solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1458 uu____1460)
        (fun uu____1463  ->
           let uu____1464 = trysolve goal solution  in
           bind uu____1464
             (fun b  ->
                if b
                then bind __dismiss (fun uu____1472  -> remove_solved_goals)
                else
                  (let uu____1474 =
                     let uu____1475 =
                       let uu____1476 = FStar_Tactics_Types.goal_env goal  in
                       tts uu____1476 solution  in
                     let uu____1477 =
                       let uu____1478 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1479 = FStar_Tactics_Types.goal_witness goal
                          in
                       tts uu____1478 uu____1479  in
                     let uu____1480 =
                       let uu____1481 = FStar_Tactics_Types.goal_env goal  in
                       let uu____1482 = FStar_Tactics_Types.goal_type goal
                          in
                       tts uu____1481 uu____1482  in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1475 uu____1477 uu____1480
                      in
                   fail uu____1474)))
  
let (solve' :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let uu____1497 = set_solution goal solution  in
      bind uu____1497
        (fun uu____1501  ->
           bind __dismiss (fun uu____1503  -> remove_solved_goals))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___103_1510 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___103_1510.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___103_1510.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___103_1510.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___103_1510.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___103_1510.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___103_1510.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___103_1510.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___103_1510.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___103_1510.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___103_1510.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1529 = FStar_Options.defensive ()  in
    if uu____1529
    then
      let b = true  in
      let env = FStar_Tactics_Types.goal_env g  in
      let b1 =
        b &&
          (let uu____1534 = FStar_Tactics_Types.goal_witness g  in
           FStar_TypeChecker_Env.closed env uu____1534)
         in
      let b2 =
        b1 &&
          (let uu____1537 = FStar_Tactics_Types.goal_type g  in
           FStar_TypeChecker_Env.closed env uu____1537)
         in
      let rec aux b3 e =
        let uu____1549 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1549 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1567 =
        (let uu____1570 = aux b2 env  in Prims.op_Negation uu____1570) &&
          (let uu____1572 = FStar_ST.op_Bang nwarn  in
           uu____1572 < (Prims.parse_int "5"))
         in
      (if uu____1567
       then
         ((let uu____1597 =
             let uu____1598 = FStar_Tactics_Types.goal_type g  in
             uu____1598.FStar_Syntax_Syntax.pos  in
           let uu____1601 =
             let uu____1606 =
               let uu____1607 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1607
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1606)  in
           FStar_Errors.log_issue uu____1597 uu____1601);
          (let uu____1608 =
             let uu____1609 = FStar_ST.op_Bang nwarn  in
             uu____1609 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1608))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___104_1677 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_1677.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_1677.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___104_1677.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_1677.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_1677.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_1677.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_1677.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_1677.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___104_1677.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___104_1677.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___105_1697 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___105_1697.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___105_1697.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___105_1697.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___105_1697.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___105_1697.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___105_1697.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___105_1697.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___105_1697.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___105_1697.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___105_1697.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___106_1717 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___106_1717.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___106_1717.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___106_1717.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___106_1717.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___106_1717.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___106_1717.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___106_1717.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___106_1717.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___106_1717.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___106_1717.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___107_1737 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___107_1737.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___107_1737.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___107_1737.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___107_1737.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___107_1737.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___107_1737.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___107_1737.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___107_1737.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___107_1737.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___107_1737.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1748  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___108_1762 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___108_1762.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___108_1762.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___108_1762.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___108_1762.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___108_1762.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___108_1762.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___108_1762.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___108_1762.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___108_1762.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___108_1762.FStar_Tactics_Types.freshness)
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
        let uu____1800 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1800 with
        | (u,ctx_uvar,g_u) ->
            let uu____1834 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1834
              (fun uu____1843  ->
                 let uu____1844 =
                   let uu____1849 =
                     let uu____1850 = FStar_List.hd ctx_uvar  in
                     FStar_Pervasives_Native.fst uu____1850  in
                   (u, uu____1849)  in
                 ret uu____1844)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1868 = FStar_Syntax_Util.un_squash t  in
    match uu____1868 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1878 =
          let uu____1879 = FStar_Syntax_Subst.compress t'  in
          uu____1879.FStar_Syntax_Syntax.n  in
        (match uu____1878 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1883 -> false)
    | uu____1884 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1894 = FStar_Syntax_Util.un_squash t  in
    match uu____1894 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1904 =
          let uu____1905 = FStar_Syntax_Subst.compress t'  in
          uu____1905.FStar_Syntax_Syntax.n  in
        (match uu____1904 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1909 -> false)
    | uu____1910 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1921  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 ->
             let uu____1932 =
               FStar_Syntax_Unionfind.find
                 (hd1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                in
             (match uu____1932 with
              | FStar_Pervasives_Native.None  -> ret hd1
              | FStar_Pervasives_Native.Some t ->
                  ((let uu____1939 = goal_to_string hd1  in
                    let uu____1940 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.print2
                      "!!!!!!!!!!!! GOAL IS ALREADY SOLVED! %s\nsol is %s\n"
                      uu____1939 uu____1940);
                   ret hd1)))
  
let (tadmit : unit -> unit tac) =
  fun uu____1947  ->
    let uu____1950 =
      let uu____1953 = cur_goal ()  in
      bind uu____1953
        (fun g  ->
           (let uu____1960 =
              let uu____1961 = FStar_Tactics_Types.goal_type g  in
              uu____1961.FStar_Syntax_Syntax.pos  in
            let uu____1964 =
              let uu____1969 =
                let uu____1970 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1970
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1969)  in
            FStar_Errors.log_issue uu____1960 uu____1964);
           solve' g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1950
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1981  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___109_1991 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___109_1991.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___109_1991.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___109_1991.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___109_1991.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___109_1991.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___109_1991.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___109_1991.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___109_1991.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___109_1991.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___109_1991.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1992 = set ps1  in
         bind uu____1992
           (fun uu____1997  ->
              let uu____1998 = FStar_BigInt.of_int_fs n1  in ret uu____1998))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____2005  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____2013 = FStar_BigInt.of_int_fs n1  in ret uu____2013)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____2026  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____2034 = FStar_BigInt.of_int_fs n1  in ret uu____2034)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____2047  ->
    let uu____2050 = cur_goal ()  in
    bind uu____2050 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____2082 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____2082 phi  in
          let uu____2083 = new_uvar reason env typ  in
          bind uu____2083
            (fun uu____2098  ->
               match uu____2098 with
               | (uu____2105,ctx_uvar) ->
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
             (fun uu____2150  ->
                let uu____2151 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____2151)
             (fun uu____2153  ->
                try
                  let uu____2173 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____2173
                with
                | FStar_Errors.Err (uu____2200,msg) ->
                    let uu____2202 = tts e t  in
                    let uu____2203 =
                      let uu____2204 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2204
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2202 uu____2203 msg
                | FStar_Errors.Error (uu____2211,msg,uu____2213) ->
                    let uu____2214 = tts e t  in
                    let uu____2215 =
                      let uu____2216 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2216
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2214 uu____2215 msg))
  
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
  fun uu____2243  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___112_2261 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___112_2261.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___112_2261.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___112_2261.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___112_2261.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___112_2261.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___112_2261.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___112_2261.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___112_2261.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___112_2261.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___112_2261.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2285 = get_guard_policy ()  in
      bind uu____2285
        (fun old_pol  ->
           let uu____2291 = set_guard_policy pol  in
           bind uu____2291
             (fun uu____2295  ->
                bind t
                  (fun r  ->
                     let uu____2299 = set_guard_policy old_pol  in
                     bind uu____2299 (fun uu____2303  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2328 =
            let uu____2329 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2329.FStar_TypeChecker_Env.guard_f  in
          match uu____2328 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2333 = istrivial e f  in
              if uu____2333
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2341 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2341
                           (fun goal  ->
                              let goal1 =
                                let uu___113_2348 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___113_2348.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___113_2348.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___113_2348.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2349 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2349
                           (fun goal  ->
                              let goal1 =
                                let uu___114_2356 = goal  in
                                {
                                  FStar_Tactics_Types.goal_main_env =
                                    (uu___114_2356.FStar_Tactics_Types.goal_main_env);
                                  FStar_Tactics_Types.goal_ctx_uvar =
                                    (uu___114_2356.FStar_Tactics_Types.goal_ctx_uvar);
                                  FStar_Tactics_Types.opts =
                                    (uu___114_2356.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2364 =
                              let uu____2365 =
                                let uu____2366 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2366
                                 in
                              Prims.op_Negation uu____2365  in
                            if uu____2364
                            then
                              mlog
                                (fun uu____2371  ->
                                   let uu____2372 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2372)
                                (fun uu____2374  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2381 ->
                              mlog
                                (fun uu____2384  ->
                                   let uu____2385 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2385)
                                (fun uu____2387  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2397 =
      let uu____2400 = cur_goal ()  in
      bind uu____2400
        (fun goal  ->
           let uu____2406 =
             let uu____2415 = FStar_Tactics_Types.goal_env goal  in
             __tc uu____2415 t  in
           bind uu____2406
             (fun uu____2427  ->
                match uu____2427 with
                | (t1,typ,guard) ->
                    let uu____2439 =
                      let uu____2442 = FStar_Tactics_Types.goal_env goal  in
                      proc_guard "tc" uu____2442 guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2439 (fun uu____2444  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2397
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2473 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2473 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2484  ->
    let uu____2487 = cur_goal ()  in
    bind uu____2487
      (fun goal  ->
         let uu____2493 =
           let uu____2494 = FStar_Tactics_Types.goal_env goal  in
           let uu____2495 = FStar_Tactics_Types.goal_type goal  in
           istrivial uu____2494 uu____2495  in
         if uu____2493
         then solve' goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2499 =
              let uu____2500 = FStar_Tactics_Types.goal_env goal  in
              let uu____2501 = FStar_Tactics_Types.goal_type goal  in
              tts uu____2500 uu____2501  in
            fail1 "Not a trivial goal: %s" uu____2499))
  
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
          FStar_List.iter
            (fun imp  ->
               match imp with
               | (s,tm,uv,rng,b) ->
                   let uu____2565 = get_uvar_solved uv  in
                   (match uu____2565 with
                    | FStar_Pervasives_Native.None  ->
                        ((let uu____2569 =
                            FStar_TypeChecker_Rel.guard_to_string e g  in
                          let uu____2570 =
                            FStar_Syntax_Print.ctx_uvar_to_string uv  in
                          FStar_Util.print3
                            "GG, implicit from guard\n>>%s\n\n(%s, %s)\n"
                            uu____2569 s uu____2570);
                         failwith "")
                    | FStar_Pervasives_Native.Some uu____2571 -> ()))
            g.FStar_TypeChecker_Env.implicits;
          (let uu____2572 =
             let uu____2573 = FStar_TypeChecker_Rel.simplify_guard e g  in
             uu____2573.FStar_TypeChecker_Env.guard_f  in
           match uu____2572 with
           | FStar_TypeChecker_Common.Trivial  ->
               ret FStar_Pervasives_Native.None
           | FStar_TypeChecker_Common.NonTrivial f ->
               let uu____2581 = istrivial e f  in
               if uu____2581
               then ret FStar_Pervasives_Native.None
               else
                 (let uu____2589 = mk_irrelevant_goal reason e f opts  in
                  bind uu____2589
                    (fun goal  ->
                       ret
                         (FStar_Pervasives_Native.Some
                            (let uu___117_2599 = goal  in
                             {
                               FStar_Tactics_Types.goal_main_env =
                                 (uu___117_2599.FStar_Tactics_Types.goal_main_env);
                               FStar_Tactics_Types.goal_ctx_uvar =
                                 (uu___117_2599.FStar_Tactics_Types.goal_ctx_uvar);
                               FStar_Tactics_Types.opts =
                                 (uu___117_2599.FStar_Tactics_Types.opts);
                               FStar_Tactics_Types.is_guard = true
                             })))))
  
let (smt : unit -> unit tac) =
  fun uu____2606  ->
    let uu____2609 = cur_goal ()  in
    bind uu____2609
      (fun g  ->
         let uu____2615 = is_irrelevant g  in
         if uu____2615
         then bind __dismiss (fun uu____2619  -> add_smt_goals [g])
         else
           (let uu____2621 =
              let uu____2622 = FStar_Tactics_Types.goal_env g  in
              let uu____2623 = FStar_Tactics_Types.goal_type g  in
              tts uu____2622 uu____2623  in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2621))
  
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
             let uu____2672 =
               try
                 let uu____2706 =
                   let uu____2715 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2715 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2706
               with | uu____2737 -> fail "divide: not enough goals"  in
             bind uu____2672
               (fun uu____2764  ->
                  match uu____2764 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___118_2790 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___118_2790.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___118_2790.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___118_2790.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___118_2790.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___118_2790.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___118_2790.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___118_2790.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___118_2790.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___118_2790.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___119_2792 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___119_2792.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___119_2792.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___119_2792.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___119_2792.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___119_2792.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___119_2792.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___119_2792.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___119_2792.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___119_2792.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2793 = set lp  in
                      bind uu____2793
                        (fun uu____2801  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2815 = set rp  in
                                     bind uu____2815
                                       (fun uu____2823  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___120_2839 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___120_2839.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___120_2839.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2840 = set p'
                                                       in
                                                    bind uu____2840
                                                      (fun uu____2848  ->
                                                         bind
                                                           remove_solved_goals
                                                           (fun uu____2854 
                                                              -> ret (a, b)))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2875 = divide FStar_BigInt.one f idtac  in
    bind uu____2875
      (fun uu____2888  -> match uu____2888 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2925::uu____2926 ->
             let uu____2929 =
               let uu____2938 = map tau  in
               divide FStar_BigInt.one tau uu____2938  in
             bind uu____2929
               (fun uu____2956  ->
                  match uu____2956 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2997 =
        bind t1
          (fun uu____3002  ->
             let uu____3003 = map t2  in
             bind uu____3003 (fun uu____3011  -> ret ()))
         in
      focus uu____2997
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____3020  ->
    let uu____3023 =
      let uu____3026 = cur_goal ()  in
      bind uu____3026
        (fun goal  ->
           let uu____3035 =
             let uu____3042 = FStar_Tactics_Types.goal_type goal  in
             FStar_Syntax_Util.arrow_one uu____3042  in
           match uu____3035 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____3051 =
                 let uu____3052 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____3052  in
               if uu____3051
               then fail "Codomain is effectful"
               else
                 (let env' =
                    let uu____3057 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.push_binders uu____3057 [b]  in
                  let typ' = comp_to_typ c  in
                  let uu____3067 = new_uvar "intro" env' typ'  in
                  bind uu____3067
                    (fun uu____3083  ->
                       match uu____3083 with
                       | (body,ctx_uvar) ->
                           let sol =
                             FStar_Syntax_Util.abs [b] body
                               FStar_Pervasives_Native.None
                              in
                           let uu____3103 = set_solution goal sol  in
                           bind uu____3103
                             (fun uu____3109  ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                   in
                                let uu____3111 = replace_cur g  in
                                bind uu____3111 (fun uu____3115  -> ret b))))
           | FStar_Pervasives_Native.None  ->
               let uu____3120 =
                 let uu____3121 = FStar_Tactics_Types.goal_env goal  in
                 let uu____3122 = FStar_Tactics_Types.goal_type goal  in
                 tts uu____3121 uu____3122  in
               fail1 "goal is not an arrow (%s)" uu____3120)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____3023
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____3137  ->
    let uu____3144 = cur_goal ()  in
    bind uu____3144
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____3161 =
            let uu____3168 = FStar_Tactics_Types.goal_type goal  in
            FStar_Syntax_Util.arrow_one uu____3168  in
          match uu____3161 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____3181 =
                let uu____3182 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____3182  in
              if uu____3181
              then fail "Codomain is effectful"
              else
                (let bv =
                   let uu____3195 = FStar_Tactics_Types.goal_type goal  in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu____3195
                    in
                 let bs =
                   let uu____3203 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____3203; b]  in
                 let env' =
                   let uu____3221 = FStar_Tactics_Types.goal_env goal  in
                   FStar_TypeChecker_Env.push_binders uu____3221 bs  in
                 let uu____3222 =
                   let uu____3229 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____3229  in
                 bind uu____3222
                   (fun uu____3248  ->
                      match uu____3248 with
                      | (u,ctx_uvar_u) ->
                          let lb =
                            let uu____3262 =
                              FStar_Tactics_Types.goal_type goal  in
                            let uu____3265 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl bv) [] uu____3262
                              FStar_Parser_Const.effect_Tot_lid uu____3265 []
                              FStar_Range.dummyRange
                             in
                          let body = FStar_Syntax_Syntax.bv_to_name bv  in
                          let uu____3279 =
                            FStar_Syntax_Subst.close_let_rec [lb] body  in
                          (match uu____3279 with
                           | (lbs,body1) ->
                               let tm =
                                 let uu____3301 =
                                   let uu____3302 =
                                     FStar_Tactics_Types.goal_witness goal
                                      in
                                   uu____3302.FStar_Syntax_Syntax.pos  in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((true, lbs), body1))
                                   FStar_Pervasives_Native.None uu____3301
                                  in
                               let uu____3315 = set_solution goal tm  in
                               bind uu____3315
                                 (fun uu____3324  ->
                                    let uu____3325 =
                                      replace_cur
                                        (let uu___123_3330 = goal  in
                                         {
                                           FStar_Tactics_Types.goal_main_env
                                             =
                                             (uu___123_3330.FStar_Tactics_Types.goal_main_env);
                                           FStar_Tactics_Types.goal_ctx_uvar
                                             = ctx_uvar_u;
                                           FStar_Tactics_Types.opts =
                                             (uu___123_3330.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___123_3330.FStar_Tactics_Types.is_guard)
                                         })
                                       in
                                    bind uu____3325
                                      (fun uu____3337  ->
                                         let uu____3338 =
                                           let uu____3343 =
                                             FStar_Syntax_Syntax.mk_binder bv
                                              in
                                           (uu____3343, b)  in
                                         ret uu____3338)))))
          | FStar_Pervasives_Native.None  ->
              let uu____3352 =
                let uu____3353 = FStar_Tactics_Types.goal_env goal  in
                let uu____3354 = FStar_Tactics_Types.goal_type goal  in
                tts uu____3353 uu____3354  in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3352))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3372 = cur_goal ()  in
    bind uu____3372
      (fun goal  ->
         mlog
           (fun uu____3379  ->
              let uu____3380 =
                let uu____3381 = FStar_Tactics_Types.goal_witness goal  in
                FStar_Syntax_Print.term_to_string uu____3381  in
              FStar_Util.print1 "norm: witness = %s\n" uu____3380)
           (fun uu____3386  ->
              let steps =
                let uu____3390 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3390
                 in
              let t =
                let uu____3394 = FStar_Tactics_Types.goal_env goal  in
                let uu____3395 = FStar_Tactics_Types.goal_type goal  in
                normalize steps uu____3394 uu____3395  in
              let uu____3396 = FStar_Tactics_Types.goal_with_type goal t  in
              replace_cur uu____3396))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3420 =
          mlog
            (fun uu____3425  ->
               let uu____3426 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3426)
            (fun uu____3428  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3434 -> g.FStar_Tactics_Types.opts
                      | uu____3437 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3442  ->
                         let uu____3443 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3443)
                      (fun uu____3446  ->
                         let uu____3447 = __tc e t  in
                         bind uu____3447
                           (fun uu____3468  ->
                              match uu____3468 with
                              | (t1,uu____3478,uu____3479) ->
                                  let steps =
                                    let uu____3483 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3483
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3420
  
let (refine_intro : unit -> unit tac) =
  fun uu____3497  ->
    let uu____3500 =
      let uu____3503 = cur_goal ()  in
      bind uu____3503
        (fun g  ->
           let uu____3510 =
             let uu____3521 = FStar_Tactics_Types.goal_env g  in
             let uu____3522 = FStar_Tactics_Types.goal_type g  in
             FStar_TypeChecker_Rel.base_and_refinement uu____3521 uu____3522
              in
           match uu____3510 with
           | (uu____3525,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 = FStar_Tactics_Types.goal_with_type g t  in
               let uu____3550 =
                 let uu____3555 =
                   let uu____3560 =
                     let uu____3561 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3561]  in
                   FStar_Syntax_Subst.open_term uu____3560 phi  in
                 match uu____3555 with
                 | (bvs,phi1) ->
                     let uu____3580 =
                       let uu____3581 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3581  in
                     (uu____3580, phi1)
                  in
               (match uu____3550 with
                | (bv1,phi1) ->
                    let uu____3594 =
                      let uu____3597 = FStar_Tactics_Types.goal_env g  in
                      let uu____3598 =
                        let uu____3599 =
                          let uu____3602 =
                            let uu____3603 =
                              let uu____3610 =
                                FStar_Tactics_Types.goal_witness g  in
                              (bv1, uu____3610)  in
                            FStar_Syntax_Syntax.NT uu____3603  in
                          [uu____3602]  in
                        FStar_Syntax_Subst.subst uu____3599 phi1  in
                      mk_irrelevant_goal "refine_intro refinement" uu____3597
                        uu____3598 g.FStar_Tactics_Types.opts
                       in
                    bind uu____3594
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3618  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3500
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3637 = cur_goal ()  in
      bind uu____3637
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               let uu____3645 = FStar_Tactics_Types.goal_env goal  in
               let uu____3646 = FStar_Tactics_Types.goal_type goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____3645 uu____3646
             else FStar_Tactics_Types.goal_env goal  in
           let uu____3648 = __tc env t  in
           bind uu____3648
             (fun uu____3667  ->
                match uu____3667 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3682  ->
                         let uu____3683 =
                           let uu____3684 = FStar_Tactics_Types.goal_env goal
                              in
                           tts uu____3684 typ  in
                         let uu____3685 =
                           let uu____3686 = FStar_Tactics_Types.goal_env goal
                              in
                           FStar_TypeChecker_Rel.guard_to_string uu____3686
                             guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3683 uu____3685)
                      (fun uu____3689  ->
                         let uu____3690 =
                           let uu____3693 = FStar_Tactics_Types.goal_env goal
                              in
                           proc_guard "__exact typing" uu____3693 guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3690
                           (fun uu____3695  ->
                              mlog
                                (fun uu____3699  ->
                                   let uu____3700 =
                                     let uu____3701 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     tts uu____3701 typ  in
                                   let uu____3702 =
                                     let uu____3703 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3704 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     tts uu____3703 uu____3704  in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3700 uu____3702)
                                (fun uu____3707  ->
                                   let uu____3708 =
                                     let uu____3711 =
                                       FStar_Tactics_Types.goal_env goal  in
                                     let uu____3712 =
                                       FStar_Tactics_Types.goal_type goal  in
                                     do_unify uu____3711 typ uu____3712  in
                                   bind uu____3708
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3718 =
                                             let uu____3719 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3719 t1  in
                                           let uu____3720 =
                                             let uu____3721 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             tts uu____3721 typ  in
                                           let uu____3722 =
                                             let uu____3723 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3724 =
                                               FStar_Tactics_Types.goal_type
                                                 goal
                                                in
                                             tts uu____3723 uu____3724  in
                                           let uu____3725 =
                                             let uu____3726 =
                                               FStar_Tactics_Types.goal_env
                                                 goal
                                                in
                                             let uu____3727 =
                                               FStar_Tactics_Types.goal_witness
                                                 goal
                                                in
                                             tts uu____3726 uu____3727  in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3718 uu____3720 uu____3722
                                             uu____3725)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3742 =
        mlog
          (fun uu____3747  ->
             let uu____3748 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3748)
          (fun uu____3751  ->
             let uu____3752 =
               let uu____3759 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3759  in
             bind uu____3752
               (fun uu___89_3768  ->
                  match uu___89_3768 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3778  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3781  ->
                           let uu____3782 =
                             let uu____3789 =
                               let uu____3792 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3792
                                 (fun uu____3797  ->
                                    let uu____3798 = refine_intro ()  in
                                    bind uu____3798
                                      (fun uu____3802  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3789  in
                           bind uu____3782
                             (fun uu___88_3809  ->
                                match uu___88_3809 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3817 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3742
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3846 =
             let uu____3849 =
               let uu____3852 = FStar_Tactics_Types.goal_type g  in
               FStar_Syntax_Free.uvars uu____3852  in
             FStar_Util.set_elements uu____3849  in
           FStar_List.map (fun u1  -> u1.FStar_Syntax_Syntax.ctx_uvar_head)
             uu____3846
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
          let uu____3930 = f x  in
          bind uu____3930
            (fun y  ->
               let uu____3938 = mapM f xs  in
               bind uu____3938 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3958 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3978 = cur_goal ()  in
        bind uu____3978
          (fun goal  ->
             mlog
               (fun uu____3985  ->
                  let uu____3986 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3986)
               (fun uu____3989  ->
                  let uu____3990 =
                    let uu____3995 =
                      let uu____3998 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3998  in
                    trytac_exn uu____3995  in
                  bind uu____3990
                    (fun uu___90_4005  ->
                       match uu___90_4005 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____4013  ->
                                let uu____4014 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____4014)
                             (fun uu____4017  ->
                                let uu____4018 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____4018 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____4042  ->
                                         let uu____4043 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____4043)
                                      (fun uu____4046  ->
                                         let uu____4047 =
                                           let uu____4048 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____4048  in
                                         if uu____4047
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____4052 =
                                              let uu____4059 =
                                                FStar_Tactics_Types.goal_env
                                                  goal
                                                 in
                                              new_uvar "apply" uu____4059
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____4052
                                              (fun uu____4070  ->
                                                 match uu____4070 with
                                                 | (u,_goal_u) ->
                                                     let tm' =
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         tm [(u, aq)]
                                                         FStar_Pervasives_Native.None
                                                         tm.FStar_Syntax_Syntax.pos
                                                        in
                                                     let typ' =
                                                       let uu____4097 =
                                                         comp_to_typ c  in
                                                       FStar_All.pipe_left
                                                         (FStar_Syntax_Subst.subst
                                                            [FStar_Syntax_Syntax.NT
                                                               (bv, u)])
                                                         uu____4097
                                                        in
                                                     let uu____4100 =
                                                       __apply uopt tm' typ'
                                                        in
                                                     bind uu____4100
                                                       (fun uu____4108  ->
                                                          let u1 =
                                                            let uu____4110 =
                                                              FStar_Tactics_Types.goal_env
                                                                goal
                                                               in
                                                            bnorm uu____4110
                                                              u
                                                             in
                                                          let uu____4111 =
                                                            let uu____4112 =
                                                              let uu____4115
                                                                =
                                                                let uu____4116
                                                                  =
                                                                  FStar_Syntax_Util.head_and_args
                                                                    u1
                                                                   in
                                                                FStar_Pervasives_Native.fst
                                                                  uu____4116
                                                                 in
                                                              FStar_Syntax_Subst.compress
                                                                uu____4115
                                                               in
                                                            uu____4112.FStar_Syntax_Syntax.n
                                                             in
                                                          match uu____4111
                                                          with
                                                          | FStar_Syntax_Syntax.Tm_uvar
                                                              (goal_u,uu____4144)
                                                              ->
                                                              bind get
                                                                (fun ps  ->
                                                                   let uu____4168
                                                                    =
                                                                    uopt &&
                                                                    (uvar_free
                                                                    goal_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    ps)  in
                                                                   if
                                                                    uu____4168
                                                                   then
                                                                    ret ()
                                                                   else
                                                                    add_goals
                                                                    [(
                                                                    let uu___124_4173
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___124_4173.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    = goal_u;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___124_4173.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    })])
                                                          | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____4228 =
        mlog
          (fun uu____4233  ->
             let uu____4234 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____4234)
          (fun uu____4237  ->
             let uu____4238 = cur_goal ()  in
             bind uu____4238
               (fun goal  ->
                  let uu____4244 =
                    let uu____4253 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4253 tm  in
                  bind uu____4244
                    (fun uu____4267  ->
                       match uu____4267 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             let uu____4280 =
                               FStar_Tactics_Types.goal_env goal  in
                             bnorm uu____4280 typ  in
                           let uu____4281 =
                             let uu____4284 =
                               let uu____4287 = __apply uopt tm1 typ1  in
                               bind uu____4287
                                 (fun uu____4292  ->
                                    let uu____4293 =
                                      FStar_Tactics_Types.goal_env goal  in
                                    proc_guard "apply guard" uu____4293 guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____4284  in
                           let uu____4294 =
                             let uu____4297 =
                               let uu____4298 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4298 tm1  in
                             let uu____4299 =
                               let uu____4300 =
                                 FStar_Tactics_Types.goal_env goal  in
                               tts uu____4300 typ1  in
                             let uu____4301 =
                               let uu____4302 =
                                 FStar_Tactics_Types.goal_env goal  in
                               let uu____4303 =
                                 FStar_Tactics_Types.goal_type goal  in
                               tts uu____4302 uu____4303  in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____4297 uu____4299 uu____4301
                              in
                           try_unif uu____4281 uu____4294)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____4228
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____4326 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____4326
    then
      let uu____4333 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____4352 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____4393 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____4333 with
      | (pre,post) ->
          let post1 =
            let uu____4429 =
              let uu____4438 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4438]  in
            FStar_Syntax_Util.mk_app post uu____4429  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4462 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4462
       then
         let uu____4469 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4469
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4502 =
      let uu____4505 =
        mlog
          (fun uu____4510  ->
             let uu____4511 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4511)
          (fun uu____4515  ->
             let is_unit_t t =
               let uu____4522 =
                 let uu____4523 = FStar_Syntax_Subst.compress t  in
                 uu____4523.FStar_Syntax_Syntax.n  in
               match uu____4522 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4527 -> false  in
             let uu____4528 = cur_goal ()  in
             bind uu____4528
               (fun goal  ->
                  let uu____4534 =
                    let uu____4543 = FStar_Tactics_Types.goal_env goal  in
                    __tc uu____4543 tm  in
                  bind uu____4534
                    (fun uu____4558  ->
                       match uu____4558 with
                       | (tm1,t,guard) ->
                           let uu____4570 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4570 with
                            | (bs,comp) ->
                                let uu____4597 = lemma_or_sq comp  in
                                (match uu____4597 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4616 =
                                       FStar_List.fold_left
                                         (fun uu____4658  ->
                                            fun uu____4659  ->
                                              match (uu____4658, uu____4659)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4750 =
                                                    is_unit_t b_t  in
                                                  if uu____4750
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4780 =
                                                       let uu____4793 =
                                                         let uu____4794 =
                                                           FStar_Tactics_Types.goal_type
                                                             goal
                                                            in
                                                         uu____4794.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____4797 =
                                                         FStar_Tactics_Types.goal_env
                                                           goal
                                                          in
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         uu____4793
                                                         uu____4797 b_t
                                                        in
                                                     match uu____4780 with
                                                     | (u,uu____4813,g_u) ->
                                                         let uu____4827 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4827,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4616 with
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
                                          let uu____4888 =
                                            let uu____4891 =
                                              FStar_Tactics_Types.goal_env
                                                goal
                                               in
                                            let uu____4892 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            let uu____4893 =
                                              FStar_Tactics_Types.goal_type
                                                goal
                                               in
                                            do_unify uu____4891 uu____4892
                                              uu____4893
                                             in
                                          bind uu____4888
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4901 =
                                                   let uu____4902 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   tts uu____4902 tm1  in
                                                 let uu____4903 =
                                                   let uu____4904 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4905 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts uu____4904 uu____4905
                                                    in
                                                 let uu____4906 =
                                                   let uu____4907 =
                                                     FStar_Tactics_Types.goal_env
                                                       goal
                                                      in
                                                   let uu____4908 =
                                                     FStar_Tactics_Types.goal_type
                                                       goal
                                                      in
                                                   tts uu____4907 uu____4908
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4901 uu____4903
                                                   uu____4906
                                               else
                                                 (let uu____4910 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4910
                                                    (fun uu____4915  ->
                                                       let uu____4916 =
                                                         solve' goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4916
                                                         (fun uu____4924  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4949
                                                                  =
                                                                  let uu____4952
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4952
                                                                   in
                                                                FStar_List.map
                                                                  (fun x  ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                  uu____4949
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
                                                                   let uu____4987
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g'  in
                                                                   is_free_uvar
                                                                    uv
                                                                    uu____4987)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____5003
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____5003
                                                              with
                                                              | (hd1,uu____5019)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____5041)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                   | 
                                                                   uu____5062
                                                                    -> false)
                                                               in
                                                            let uu____5063 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____5133
                                                                     ->
                                                                    match uu____5133
                                                                    with
                                                                    | 
                                                                    (_msg,term,ctx_uvar,_range,uu____5158)
                                                                    ->
                                                                    let uu____5159
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____5159
                                                                    with
                                                                    | 
                                                                    (hd1,uu____5185)
                                                                    ->
                                                                    let uu____5206
                                                                    =
                                                                    let uu____5207
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____5207.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____5206
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (ctx_uvar1,uu____5221)
                                                                    ->
                                                                    let env =
                                                                    let uu___127_5243
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___127_5243.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let goal_ty
                                                                    =
                                                                    bnorm env
                                                                    ctx_uvar1.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    let goal1
                                                                    =
                                                                    FStar_Tactics_Types.goal_with_type
                                                                    (let uu___128_5248
                                                                    = goal
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.goal_main_env
                                                                    =
                                                                    (uu___128_5248.FStar_Tactics_Types.goal_main_env);
                                                                    FStar_Tactics_Types.goal_ctx_uvar
                                                                    =
                                                                    ctx_uvar1;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___128_5248.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___128_5248.FStar_Tactics_Types.is_guard)
                                                                    })
                                                                    goal_ty
                                                                     in
                                                                    ret
                                                                    ([goal1],
                                                                    [])
                                                                    | 
                                                                    uu____5261
                                                                    ->
                                                                    let env =
                                                                    let uu___129_5263
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.lax);
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.dep_graph
                                                                    =
                                                                    (uu___129_5263.FStar_TypeChecker_Env.dep_graph)
                                                                    }  in
                                                                    let g_typ
                                                                    =
                                                                    let uu____5265
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____5265
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
                                                                    let uu____5268
                                                                    =
                                                                    let uu____5275
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____5275
                                                                    term1  in
                                                                    match uu____5268
                                                                    with
                                                                    | 
                                                                    (uu____5276,uu____5277,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____5279
                                                                    =
                                                                    let uu____5284
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    uu____5284
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____5279
                                                                    (fun
                                                                    uu___91_5296
                                                                     ->
                                                                    match uu___91_5296
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
                                                            bind uu____5063
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____5364
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5364
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____5386
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____5386
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5447
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5447
                                                                    then
                                                                    let uu____5450
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5450
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
                                                                    let uu____5464
                                                                    =
                                                                    let uu____5465
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g  in
                                                                    checkone
                                                                    uu____5465
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5464)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5466
                                                                   =
                                                                   let uu____5469
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    uu____5469
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5466
                                                                   (fun
                                                                    uu____5472
                                                                     ->
                                                                    let uu____5473
                                                                    =
                                                                    let uu____5476
                                                                    =
                                                                    let uu____5477
                                                                    =
                                                                    let uu____5478
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    let uu____5479
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    uu____5478
                                                                    uu____5479
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5477
                                                                     in
                                                                    if
                                                                    uu____5476
                                                                    then
                                                                    let uu____5482
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    goal  in
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    uu____5482
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5473
                                                                    (fun
                                                                    uu____5486
                                                                     ->
                                                                    let uu____5487
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5487
                                                                    (fun
                                                                    uu____5491
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4505  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4502
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5513 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5513 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5523::(e1,uu____5525)::(e2,uu____5527)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5570 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5594 = destruct_eq' typ  in
    match uu____5594 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5624 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5624 with
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
        let uu____5686 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5686 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5734 = aux e'  in
               FStar_Util.map_opt uu____5734
                 (fun uu____5758  ->
                    match uu____5758 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5779 = aux e  in
      FStar_Util.map_opt uu____5779
        (fun uu____5803  ->
           match uu____5803 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5870 =
            let uu____5879 = FStar_Tactics_Types.goal_env g  in
            split_env b1 uu____5879  in
          FStar_Util.map_opt uu____5870
            (fun uu____5894  ->
               match uu____5894 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___130_5913 = bv  in
                     let uu____5914 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___130_5913.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___130_5913.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5914
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let new_env = push_bvs e0 (b2 :: bvs1)  in
                   let new_goal =
                     let uu___131_5922 = g.FStar_Tactics_Types.goal_ctx_uvar
                        in
                     let uu____5923 =
                       FStar_TypeChecker_Env.all_binders new_env  in
                     let uu____5930 =
                       let uu____5933 = FStar_Tactics_Types.goal_type g  in
                       FStar_Syntax_Subst.subst s uu____5933  in
                     {
                       FStar_Syntax_Syntax.ctx_uvar_head =
                         (uu___131_5922.FStar_Syntax_Syntax.ctx_uvar_head);
                       FStar_Syntax_Syntax.ctx_uvar_gamma =
                         (new_env.FStar_TypeChecker_Env.gamma);
                       FStar_Syntax_Syntax.ctx_uvar_binders = uu____5923;
                       FStar_Syntax_Syntax.ctx_uvar_typ = uu____5930;
                       FStar_Syntax_Syntax.ctx_uvar_reason =
                         (uu___131_5922.FStar_Syntax_Syntax.ctx_uvar_reason);
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         (uu___131_5922.FStar_Syntax_Syntax.ctx_uvar_should_check);
                       FStar_Syntax_Syntax.ctx_uvar_range =
                         (uu___131_5922.FStar_Syntax_Syntax.ctx_uvar_range)
                     }  in
                   let uu___132_5934 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___132_5934.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar = new_goal;
                     FStar_Tactics_Types.opts =
                       (uu___132_5934.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___132_5934.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5944 =
      let uu____5947 = cur_goal ()  in
      bind uu____5947
        (fun goal  ->
           let uu____5955 = h  in
           match uu____5955 with
           | (bv,uu____5959) ->
               mlog
                 (fun uu____5963  ->
                    let uu____5964 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5965 =
                      let uu____5966 = FStar_Tactics_Types.goal_env goal  in
                      tts uu____5966 bv.FStar_Syntax_Syntax.sort  in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5964
                      uu____5965)
                 (fun uu____5969  ->
                    let uu____5970 =
                      let uu____5979 = FStar_Tactics_Types.goal_env goal  in
                      split_env bv uu____5979  in
                    match uu____5970 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____6000 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____6000 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____6015 =
                               let uu____6016 = FStar_Syntax_Subst.compress x
                                  in
                               uu____6016.FStar_Syntax_Syntax.n  in
                             (match uu____6015 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___133_6033 = bv1  in
                                    let uu____6034 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___133_6033.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___133_6033.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____6034
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let new_env = push_bvs e0 (bv :: bvs1)  in
                                  let new_goal =
                                    let uu___134_6042 =
                                      goal.FStar_Tactics_Types.goal_ctx_uvar
                                       in
                                    let uu____6043 =
                                      FStar_TypeChecker_Env.all_binders
                                        new_env
                                       in
                                    let uu____6050 =
                                      let uu____6053 =
                                        FStar_Tactics_Types.goal_type goal
                                         in
                                      FStar_Syntax_Subst.subst s uu____6053
                                       in
                                    {
                                      FStar_Syntax_Syntax.ctx_uvar_head =
                                        (uu___134_6042.FStar_Syntax_Syntax.ctx_uvar_head);
                                      FStar_Syntax_Syntax.ctx_uvar_gamma =
                                        (new_env.FStar_TypeChecker_Env.gamma);
                                      FStar_Syntax_Syntax.ctx_uvar_binders =
                                        uu____6043;
                                      FStar_Syntax_Syntax.ctx_uvar_typ =
                                        uu____6050;
                                      FStar_Syntax_Syntax.ctx_uvar_reason =
                                        (uu___134_6042.FStar_Syntax_Syntax.ctx_uvar_reason);
                                      FStar_Syntax_Syntax.ctx_uvar_should_check
                                        =
                                        (uu___134_6042.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                      FStar_Syntax_Syntax.ctx_uvar_range =
                                        (uu___134_6042.FStar_Syntax_Syntax.ctx_uvar_range)
                                    }  in
                                  replace_cur
                                    (let uu___135_6056 = goal  in
                                     {
                                       FStar_Tactics_Types.goal_main_env =
                                         (uu___135_6056.FStar_Tactics_Types.goal_main_env);
                                       FStar_Tactics_Types.goal_ctx_uvar =
                                         new_goal;
                                       FStar_Tactics_Types.opts =
                                         (uu___135_6056.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___135_6056.FStar_Tactics_Types.is_guard)
                                     })
                              | uu____6057 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____6058 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5944
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____6083 =
        let uu____6086 = cur_goal ()  in
        bind uu____6086
          (fun goal  ->
             let uu____6097 = b  in
             match uu____6097 with
             | (bv,uu____6101) ->
                 let bv' =
                   let uu____6103 =
                     let uu___136_6104 = bv  in
                     let uu____6105 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____6105;
                       FStar_Syntax_Syntax.index =
                         (uu___136_6104.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___136_6104.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____6103  in
                 let s1 =
                   let uu____6109 =
                     let uu____6110 =
                       let uu____6117 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____6117)  in
                     FStar_Syntax_Syntax.NT uu____6110  in
                   [uu____6109]  in
                 let uu____6122 = subst_goal bv bv' s1 goal  in
                 (match uu____6122 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____6083
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____6141 =
      let uu____6144 = cur_goal ()  in
      bind uu____6144
        (fun goal  ->
           let uu____6153 = b  in
           match uu____6153 with
           | (bv,uu____6157) ->
               let uu____6158 =
                 let uu____6167 = FStar_Tactics_Types.goal_env goal  in
                 split_env bv uu____6167  in
               (match uu____6158 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____6188 = FStar_Syntax_Util.type_u ()  in
                    (match uu____6188 with
                     | (ty,u) ->
                         let uu____6197 = new_uvar "binder_retype" e0 ty  in
                         bind uu____6197
                           (fun uu____6215  ->
                              match uu____6215 with
                              | (t',u_t') ->
                                  let bv'' =
                                    let uu___137_6225 = bv  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___137_6225.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___137_6225.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t'
                                    }  in
                                  let s =
                                    let uu____6229 =
                                      let uu____6230 =
                                        let uu____6237 =
                                          FStar_Syntax_Syntax.bv_to_name bv''
                                           in
                                        (bv, uu____6237)  in
                                      FStar_Syntax_Syntax.NT uu____6230  in
                                    [uu____6229]  in
                                  let bvs1 =
                                    FStar_List.map
                                      (fun b1  ->
                                         let uu___138_6249 = b1  in
                                         let uu____6250 =
                                           FStar_Syntax_Subst.subst s
                                             b1.FStar_Syntax_Syntax.sort
                                            in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___138_6249.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___138_6249.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             uu____6250
                                         }) bvs
                                     in
                                  let env' = push_bvs e0 (bv'' :: bvs1)  in
                                  bind __dismiss
                                    (fun uu____6257  ->
                                       let new_goal =
                                         let uu____6259 =
                                           FStar_Tactics_Types.goal_with_env
                                             goal env'
                                            in
                                         let uu____6260 =
                                           let uu____6261 =
                                             FStar_Tactics_Types.goal_type
                                               goal
                                              in
                                           FStar_Syntax_Subst.subst s
                                             uu____6261
                                            in
                                         FStar_Tactics_Types.goal_with_type
                                           uu____6259 uu____6260
                                          in
                                       let uu____6262 = add_goals [new_goal]
                                          in
                                       bind uu____6262
                                         (fun uu____6267  ->
                                            let uu____6268 =
                                              FStar_Syntax_Util.mk_eq2
                                                (FStar_Syntax_Syntax.U_succ u)
                                                ty
                                                bv.FStar_Syntax_Syntax.sort
                                                t'
                                               in
                                            add_irrelevant_goal
                                              "binder_retype equation" e0
                                              uu____6268
                                              goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____6141
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____6291 =
        let uu____6294 = cur_goal ()  in
        bind uu____6294
          (fun goal  ->
             let uu____6303 = b  in
             match uu____6303 with
             | (bv,uu____6307) ->
                 let uu____6308 =
                   let uu____6317 = FStar_Tactics_Types.goal_env goal  in
                   split_env bv uu____6317  in
                 (match uu____6308 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____6341 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____6341
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___139_6346 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___139_6346.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___139_6346.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      let uu____6348 =
                        FStar_Tactics_Types.goal_with_env goal env'  in
                      replace_cur uu____6348))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____6291
  
let (revert : unit -> unit tac) =
  fun uu____6359  ->
    let uu____6362 = cur_goal ()  in
    bind uu____6362
      (fun goal  ->
         let uu____6368 =
           let uu____6375 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6375  in
         match uu____6368 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____6391 =
                 let uu____6394 = FStar_Tactics_Types.goal_type goal  in
                 FStar_Syntax_Syntax.mk_Total uu____6394  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____6391
                in
             let uu____6403 = new_uvar "revert" env' typ'  in
             bind uu____6403
               (fun uu____6418  ->
                  match uu____6418 with
                  | (r,u_r) ->
                      let uu____6427 =
                        let uu____6430 =
                          let uu____6431 =
                            let uu____6432 =
                              FStar_Tactics_Types.goal_type goal  in
                            uu____6432.FStar_Syntax_Syntax.pos  in
                          let uu____6435 =
                            let uu____6440 =
                              let uu____6441 =
                                let uu____6448 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____6448  in
                              [uu____6441]  in
                            FStar_Syntax_Syntax.mk_Tm_app r uu____6440  in
                          uu____6435 FStar_Pervasives_Native.None uu____6431
                           in
                        set_solution goal uu____6430  in
                      bind uu____6427
                        (fun uu____6465  ->
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
      let uu____6477 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____6477
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____6490 = cur_goal ()  in
    bind uu____6490
      (fun goal  ->
         mlog
           (fun uu____6498  ->
              let uu____6499 = FStar_Syntax_Print.binder_to_string b  in
              let uu____6500 =
                let uu____6501 =
                  let uu____6502 =
                    let uu____6509 = FStar_Tactics_Types.goal_env goal  in
                    FStar_TypeChecker_Env.all_binders uu____6509  in
                  FStar_All.pipe_right uu____6502 FStar_List.length  in
                FStar_All.pipe_right uu____6501 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____6499 uu____6500)
           (fun uu____6522  ->
              let uu____6523 =
                let uu____6532 = FStar_Tactics_Types.goal_env goal  in
                split_env bv uu____6532  in
              match uu____6523 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6571 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6571
                        then
                          let uu____6574 =
                            let uu____6575 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6575
                             in
                          fail uu____6574
                        else check1 bvs2
                     in
                  let uu____6577 =
                    let uu____6578 = FStar_Tactics_Types.goal_type goal  in
                    free_in bv uu____6578  in
                  if uu____6577
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6582 = check1 bvs  in
                     bind uu____6582
                       (fun uu____6588  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6590 =
                            let uu____6597 =
                              FStar_Tactics_Types.goal_type goal  in
                            new_uvar "clear.witness" env' uu____6597  in
                          bind uu____6590
                            (fun uu____6606  ->
                               match uu____6606 with
                               | (ut,uvar_ut) ->
                                   let uu____6615 = set_solution goal ut  in
                                   bind uu____6615
                                     (fun uu____6620  ->
                                        let uu____6621 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                           in
                                        replace_cur uu____6621))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6628  ->
    let uu____6631 = cur_goal ()  in
    bind uu____6631
      (fun goal  ->
         let uu____6637 =
           let uu____6644 = FStar_Tactics_Types.goal_env goal  in
           FStar_TypeChecker_Env.pop_bv uu____6644  in
         match uu____6637 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6652) ->
             let uu____6657 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6657)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6667 = cur_goal ()  in
    bind uu____6667
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6677 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6677  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6680  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6690 = cur_goal ()  in
    bind uu____6690
      (fun g  ->
         let ctx = FStar_Tactics_Types.goal_env g  in
         let ctx' =
           let uu____6700 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6700  in
         let g' = FStar_Tactics_Types.goal_with_env g ctx'  in
         bind __dismiss (fun uu____6703  -> add_goals [g']))
  
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
            let uu____6743 = FStar_Syntax_Subst.compress t  in
            uu____6743.FStar_Syntax_Syntax.n  in
          let uu____6746 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___143_6752 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___143_6752.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___143_6752.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6746
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6768 =
                   let uu____6769 = FStar_Syntax_Subst.compress t1  in
                   uu____6769.FStar_Syntax_Syntax.n  in
                 match uu____6768 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6796 = ff hd1  in
                     bind uu____6796
                       (fun hd2  ->
                          let fa uu____6818 =
                            match uu____6818 with
                            | (a,q) ->
                                let uu____6831 = ff a  in
                                bind uu____6831 (fun a1  -> ret (a1, q))
                             in
                          let uu____6844 = mapM fa args  in
                          bind uu____6844
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6910 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6910 with
                      | (bs1,t') ->
                          let uu____6919 =
                            let uu____6922 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6922 t'  in
                          bind uu____6919
                            (fun t''  ->
                               let uu____6926 =
                                 let uu____6927 =
                                   let uu____6944 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6951 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6944, uu____6951, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6927  in
                               ret uu____6926))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____7020 = ff hd1  in
                     bind uu____7020
                       (fun hd2  ->
                          let ffb br =
                            let uu____7035 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____7035 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____7067 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____7067  in
                                let uu____7068 = ff1 e  in
                                bind uu____7068
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____7083 = mapM ffb brs  in
                          bind uu____7083
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____7127;
                          FStar_Syntax_Syntax.lbtyp = uu____7128;
                          FStar_Syntax_Syntax.lbeff = uu____7129;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____7131;
                          FStar_Syntax_Syntax.lbpos = uu____7132;_}::[]),e)
                     ->
                     let lb =
                       let uu____7157 =
                         let uu____7158 = FStar_Syntax_Subst.compress t1  in
                         uu____7158.FStar_Syntax_Syntax.n  in
                       match uu____7157 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____7162) -> lb
                       | uu____7175 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____7184 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7184
                         (fun def1  ->
                            ret
                              (let uu___140_7190 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___140_7190.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___140_7190.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___140_7190.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___140_7190.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___140_7190.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___140_7190.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7191 = fflb lb  in
                     bind uu____7191
                       (fun lb1  ->
                          let uu____7201 =
                            let uu____7206 =
                              let uu____7207 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____7207]  in
                            FStar_Syntax_Subst.open_term uu____7206 e  in
                          match uu____7201 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____7231 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____7231  in
                              let uu____7232 = ff1 e1  in
                              bind uu____7232
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____7273 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____7273
                         (fun def  ->
                            ret
                              (let uu___141_7279 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___141_7279.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___141_7279.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___141_7279.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___141_7279.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___141_7279.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___141_7279.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____7280 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____7280 with
                      | (lbs1,e1) ->
                          let uu____7295 = mapM fflb lbs1  in
                          bind uu____7295
                            (fun lbs2  ->
                               let uu____7307 = ff e1  in
                               bind uu____7307
                                 (fun e2  ->
                                    let uu____7315 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____7315 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____7383 = ff t2  in
                     bind uu____7383
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____7414 = ff t2  in
                     bind uu____7414
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____7421 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___142_7428 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___142_7428.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___142_7428.FStar_Syntax_Syntax.vars)
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
            let uu____7465 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____7465 with
            | (t1,lcomp,g) ->
                let uu____7477 =
                  (let uu____7480 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____7480) ||
                    (let uu____7482 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____7482)
                   in
                if uu____7477
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____7490 = new_uvar "pointwise_rec" env typ  in
                     bind uu____7490
                       (fun uu____7506  ->
                          match uu____7506 with
                          | (ut,uvar_ut) ->
                              (log ps
                                 (fun uu____7519  ->
                                    let uu____7520 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____7521 =
                                      FStar_Syntax_Print.term_to_string ut
                                       in
                                    FStar_Util.print2
                                      "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                      uu____7520 uu____7521);
                               (let uu____7522 =
                                  let uu____7525 =
                                    let uu____7526 =
                                      FStar_TypeChecker_TcTerm.universe_of
                                        env typ
                                       in
                                    FStar_Syntax_Util.mk_eq2 uu____7526 typ
                                      t1 ut
                                     in
                                  add_irrelevant_goal
                                    "pointwise_rec equation" env uu____7525
                                    opts
                                   in
                                bind uu____7522
                                  (fun uu____7529  ->
                                     let uu____7530 =
                                       bind tau
                                         (fun uu____7536  ->
                                            let ut1 =
                                              FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                env ut
                                               in
                                            log ps
                                              (fun uu____7542  ->
                                                 let uu____7543 =
                                                   FStar_Syntax_Print.term_to_string
                                                     t1
                                                    in
                                                 let uu____7544 =
                                                   FStar_Syntax_Print.term_to_string
                                                     ut1
                                                    in
                                                 FStar_Util.print2
                                                   "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                   uu____7543 uu____7544);
                                            ret ut1)
                                        in
                                     focus uu____7530))))
                      in
                   let uu____7545 = trytac' rewrite_eq  in
                   bind uu____7545
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
          let uu____7743 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7743
            (fun t1  ->
               let uu____7751 =
                 f env
                   (let uu___146_7760 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___146_7760.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___146_7760.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7751
                 (fun uu____7776  ->
                    match uu____7776 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7799 =
                               let uu____7800 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7800.FStar_Syntax_Syntax.n  in
                             match uu____7799 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7833 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7833
                                   (fun uu____7858  ->
                                      match uu____7858 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7874 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7874
                                            (fun uu____7901  ->
                                               match uu____7901 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___144_7931 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___144_7931.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___144_7931.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7967 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7967 with
                                  | (bs1,t') ->
                                      let uu____7982 =
                                        let uu____7989 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7989 ctrl1 t'
                                         in
                                      bind uu____7982
                                        (fun uu____8007  ->
                                           match uu____8007 with
                                           | (t'',ctrl2) ->
                                               let uu____8022 =
                                                 let uu____8029 =
                                                   let uu___145_8032 = t4  in
                                                   let uu____8035 =
                                                     let uu____8036 =
                                                       let uu____8053 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____8060 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____8053,
                                                         uu____8060, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____8036
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____8035;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___145_8032.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___145_8032.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____8029, ctrl2)  in
                                               ret uu____8022))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____8107 -> ret (t3, ctrl1))))

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
              let uu____8150 = ctrl_tac_fold f env ctrl t  in
              bind uu____8150
                (fun uu____8174  ->
                   match uu____8174 with
                   | (t1,ctrl1) ->
                       let uu____8189 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____8189
                         (fun uu____8216  ->
                            match uu____8216 with
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
              let uu____8298 =
                let uu____8305 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____8305
                  (fun uu____8314  ->
                     let uu____8315 = ctrl t1  in
                     bind uu____8315
                       (fun res  ->
                          let uu____8338 = trivial ()  in
                          bind uu____8338 (fun uu____8346  -> ret res)))
                 in
              bind uu____8298
                (fun uu____8362  ->
                   match uu____8362 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____8386 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____8386 with
                          | (t2,lcomp,g) ->
                              let uu____8402 =
                                (let uu____8405 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____8405) ||
                                  (let uu____8407 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____8407)
                                 in
                              if uu____8402
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____8420 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____8420
                                   (fun uu____8440  ->
                                      match uu____8440 with
                                      | (ut,uvar_ut) ->
                                          (log ps
                                             (fun uu____8457  ->
                                                let uu____8458 =
                                                  FStar_Syntax_Print.term_to_string
                                                    t2
                                                   in
                                                let uu____8459 =
                                                  FStar_Syntax_Print.term_to_string
                                                    ut
                                                   in
                                                FStar_Util.print2
                                                  "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                                  uu____8458 uu____8459);
                                           (let uu____8460 =
                                              let uu____8463 =
                                                let uu____8464 =
                                                  FStar_TypeChecker_TcTerm.universe_of
                                                    env typ
                                                   in
                                                FStar_Syntax_Util.mk_eq2
                                                  uu____8464 typ t2 ut
                                                 in
                                              add_irrelevant_goal
                                                "rewrite_rec equation" env
                                                uu____8463 opts
                                               in
                                            bind uu____8460
                                              (fun uu____8471  ->
                                                 let uu____8472 =
                                                   bind rewriter
                                                     (fun uu____8486  ->
                                                        let ut1 =
                                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                            env ut
                                                           in
                                                        log ps
                                                          (fun uu____8492  ->
                                                             let uu____8493 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t2
                                                                in
                                                             let uu____8494 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 ut1
                                                                in
                                                             FStar_Util.print2
                                                               "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                               uu____8493
                                                               uu____8494);
                                                        ret (ut1, ctrl1))
                                                    in
                                                 focus uu____8472)))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____8535 =
        bind get
          (fun ps  ->
             let uu____8545 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8545 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8582  ->
                       let uu____8583 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____8583);
                  bind dismiss_all
                    (fun uu____8586  ->
                       let uu____8587 =
                         let uu____8594 = FStar_Tactics_Types.goal_env g  in
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts) uu____8594
                           keepGoing gt1
                          in
                       bind uu____8587
                         (fun uu____8606  ->
                            match uu____8606 with
                            | (gt',uu____8614) ->
                                (log ps
                                   (fun uu____8618  ->
                                      let uu____8619 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____8619);
                                 (let uu____8620 = push_goals gs  in
                                  bind uu____8620
                                    (fun uu____8625  ->
                                       let uu____8626 =
                                         let uu____8629 =
                                           FStar_Tactics_Types.goal_with_type
                                             g gt'
                                            in
                                         [uu____8629]  in
                                       add_goals uu____8626)))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____8535
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____8652 =
        bind get
          (fun ps  ->
             let uu____8662 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____8662 with
             | (g,gs) ->
                 let gt1 = FStar_Tactics_Types.goal_type g  in
                 (log ps
                    (fun uu____8699  ->
                       let uu____8700 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8700);
                  bind dismiss_all
                    (fun uu____8703  ->
                       let uu____8704 =
                         let uu____8707 = FStar_Tactics_Types.goal_env g  in
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           uu____8707 gt1
                          in
                       bind uu____8704
                         (fun gt'  ->
                            log ps
                              (fun uu____8715  ->
                                 let uu____8716 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8716);
                            (let uu____8717 = push_goals gs  in
                             bind uu____8717
                               (fun uu____8722  ->
                                  let uu____8723 =
                                    let uu____8726 =
                                      FStar_Tactics_Types.goal_with_type g
                                        gt'
                                       in
                                    [uu____8726]  in
                                  add_goals uu____8723))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____8652
  
let (trefl : unit -> unit tac) =
  fun uu____8737  ->
    let uu____8740 =
      let uu____8743 = cur_goal ()  in
      bind uu____8743
        (fun g  ->
           let uu____8761 =
             let uu____8766 = FStar_Tactics_Types.goal_type g  in
             FStar_Syntax_Util.un_squash uu____8766  in
           match uu____8761 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8774 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8774 with
                | (hd1,args) ->
                    let uu____8807 =
                      let uu____8818 =
                        let uu____8819 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8819.FStar_Syntax_Syntax.n  in
                      (uu____8818, args)  in
                    (match uu____8807 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8831::(l,uu____8833)::(r,uu____8835)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8862 =
                           let uu____8865 = FStar_Tactics_Types.goal_env g
                              in
                           do_unify uu____8865 l r  in
                         bind uu____8862
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8872 =
                                  let uu____8873 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8873 l  in
                                let uu____8874 =
                                  let uu____8875 =
                                    FStar_Tactics_Types.goal_env g  in
                                  tts uu____8875 r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8872 uu____8874
                              else solve' g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8878) ->
                         let uu____8891 =
                           let uu____8892 = FStar_Tactics_Types.goal_env g
                              in
                           tts uu____8892 t  in
                         fail1 "trefl: not an equality (%s)" uu____8891))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8740
  
let (dup : unit -> unit tac) =
  fun uu____8905  ->
    let uu____8908 = cur_goal ()  in
    bind uu____8908
      (fun g  ->
         let uu____8914 =
           let uu____8921 = FStar_Tactics_Types.goal_env g  in
           let uu____8922 = FStar_Tactics_Types.goal_type g  in
           new_uvar "dup" uu____8921 uu____8922  in
         bind uu____8914
           (fun uu____8931  ->
              match uu____8931 with
              | (u,u_uvar) ->
                  let g' =
                    let uu___147_8941 = g  in
                    {
                      FStar_Tactics_Types.goal_main_env =
                        (uu___147_8941.FStar_Tactics_Types.goal_main_env);
                      FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                      FStar_Tactics_Types.opts =
                        (uu___147_8941.FStar_Tactics_Types.opts);
                      FStar_Tactics_Types.is_guard =
                        (uu___147_8941.FStar_Tactics_Types.is_guard)
                    }  in
                  bind __dismiss
                    (fun uu____8944  ->
                       let uu____8945 =
                         let uu____8948 = FStar_Tactics_Types.goal_env g  in
                         let uu____8949 =
                           let uu____8950 =
                             let uu____8951 = FStar_Tactics_Types.goal_env g
                                in
                             let uu____8952 = FStar_Tactics_Types.goal_type g
                                in
                             FStar_TypeChecker_TcTerm.universe_of uu____8951
                               uu____8952
                              in
                           let uu____8953 = FStar_Tactics_Types.goal_type g
                              in
                           let uu____8954 =
                             FStar_Tactics_Types.goal_witness g  in
                           FStar_Syntax_Util.mk_eq2 uu____8950 uu____8953 u
                             uu____8954
                            in
                         add_irrelevant_goal "dup equation" uu____8948
                           uu____8949 g.FStar_Tactics_Types.opts
                          in
                       bind uu____8945
                         (fun uu____8957  ->
                            let uu____8958 = add_goals [g']  in
                            bind uu____8958 (fun uu____8962  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8969  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___148_8986 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___148_8986.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___148_8986.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___148_8986.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___148_8986.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___148_8986.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___148_8986.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___148_8986.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___148_8986.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___148_8986.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___148_8986.FStar_Tactics_Types.freshness)
                })
         | uu____8987 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8996  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___149_9009 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___149_9009.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___149_9009.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___149_9009.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___149_9009.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___149_9009.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___149_9009.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___149_9009.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___149_9009.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___149_9009.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___149_9009.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____9016  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____9023 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____9043 =
      let uu____9050 = cur_goal ()  in
      bind uu____9050
        (fun g  ->
           let uu____9060 =
             let uu____9069 = FStar_Tactics_Types.goal_env g  in
             __tc uu____9069 t  in
           bind uu____9060
             (fun uu____9097  ->
                match uu____9097 with
                | (t1,typ,guard) ->
                    let uu____9113 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____9113 with
                     | (hd1,args) ->
                         let uu____9156 =
                           let uu____9169 =
                             let uu____9170 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____9170.FStar_Syntax_Syntax.n  in
                           (uu____9169, args)  in
                         (match uu____9156 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____9189)::(q,uu____9191)::[]) when
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
                                let uu____9229 =
                                  let uu____9230 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9230
                                    v_p
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9229
                                 in
                              let g2 =
                                let uu____9232 =
                                  let uu____9233 =
                                    FStar_Tactics_Types.goal_env g  in
                                  FStar_TypeChecker_Env.push_bv uu____9233
                                    v_q
                                   in
                                FStar_Tactics_Types.goal_with_env g
                                  uu____9232
                                 in
                              bind __dismiss
                                (fun uu____9240  ->
                                   let uu____9241 = add_goals [g1; g2]  in
                                   bind uu____9241
                                     (fun uu____9250  ->
                                        let uu____9251 =
                                          let uu____9256 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____9257 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____9256, uu____9257)  in
                                        ret uu____9251))
                          | uu____9262 ->
                              let uu____9275 =
                                let uu____9276 =
                                  FStar_Tactics_Types.goal_env g  in
                                tts uu____9276 typ  in
                              fail1 "Not a disjunction: %s" uu____9275))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____9043
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____9306 =
      let uu____9309 = cur_goal ()  in
      bind uu____9309
        (fun g  ->
           FStar_Options.push ();
           (let uu____9322 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____9322);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___150_9329 = g  in
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (uu___150_9329.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (uu___150_9329.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___150_9329.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____9306
  
let (top_env : unit -> env tac) =
  fun uu____9341  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____9354  ->
    let uu____9357 = cur_goal ()  in
    bind uu____9357
      (fun g  ->
         let uu____9363 = FStar_Tactics_Types.goal_env g  in
         FStar_All.pipe_left ret uu____9363)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9372  ->
    let uu____9375 = cur_goal ()  in
    bind uu____9375
      (fun g  ->
         let uu____9381 = FStar_Tactics_Types.goal_type g  in
         FStar_All.pipe_left ret uu____9381)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____9390  ->
    let uu____9393 = cur_goal ()  in
    bind uu____9393
      (fun g  ->
         let uu____9399 = FStar_Tactics_Types.goal_witness g  in
         FStar_All.pipe_left ret uu____9399)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____9416 =
        let uu____9419 = cur_goal ()  in
        bind uu____9419
          (fun goal  ->
             let env =
               let uu____9427 = FStar_Tactics_Types.goal_env goal  in
               FStar_TypeChecker_Env.set_expected_typ uu____9427 ty  in
             let uu____9428 = __tc env tm  in
             bind uu____9428
               (fun uu____9448  ->
                  match uu____9448 with
                  | (tm1,typ,guard) ->
                      let uu____9460 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____9460 (fun uu____9464  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____9416
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____9487 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____9493 =
              let uu____9500 =
                let uu____9501 = FStar_Syntax_Util.type_u ()  in
                FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9501
                 in
              new_uvar "uvar_env.2" env uu____9500  in
            bind uu____9493
              (fun uu____9517  ->
                 match uu____9517 with | (typ,uvar_typ) -> ret typ)
         in
      bind uu____9487
        (fun typ  ->
           let uu____9529 = new_uvar "uvar_env" env typ  in
           bind uu____9529
             (fun uu____9543  -> match uu____9543 with | (t,uvar_t) -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____9561 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____9580 -> g.FStar_Tactics_Types.opts
             | uu____9583 -> FStar_Options.peek ()  in
           let uu____9586 = FStar_Syntax_Util.head_and_args t  in
           match uu____9586 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar,uu____9604);
                FStar_Syntax_Syntax.pos = uu____9605;
                FStar_Syntax_Syntax.vars = uu____9606;_},uu____9607)
               ->
               let env1 =
                 let uu___151_9649 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___151_9649.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___151_9649.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___151_9649.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___151_9649.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___151_9649.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___151_9649.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___151_9649.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___151_9649.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___151_9649.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___151_9649.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___151_9649.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___151_9649.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___151_9649.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (uu___151_9649.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___151_9649.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___151_9649.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___151_9649.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___151_9649.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___151_9649.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___151_9649.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.failhard =
                     (uu___151_9649.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___151_9649.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___151_9649.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___151_9649.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___151_9649.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___151_9649.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___151_9649.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___151_9649.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___151_9649.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___151_9649.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___151_9649.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___151_9649.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___151_9649.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___151_9649.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___151_9649.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___151_9649.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.dep_graph =
                     (uu___151_9649.FStar_TypeChecker_Env.dep_graph)
                 }  in
               let g = FStar_Tactics_Types.mk_goal env1 ctx_uvar opts false
                  in
               let g1 =
                 let uu____9652 =
                   bnorm env1 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
                 FStar_Tactics_Types.goal_with_type g uu____9652  in
               add_goals [g1]
           | uu____9653 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____9561
  
let (unify :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun t1  ->
    fun t2  ->
      bind get
        (fun ps  -> do_unify ps.FStar_Tactics_Types.main_context t1 t2)
  
let (launch_process :
  Prims.string -> Prims.string Prims.list -> Prims.string -> Prims.string tac)
  =
  fun prog  ->
    fun args  ->
      fun input  ->
        bind idtac
          (fun uu____9714  ->
             let uu____9715 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____9715
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
        (fun uu____9736  ->
           let uu____9737 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9737)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9747 =
      mlog
        (fun uu____9752  ->
           let uu____9753 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9753)
        (fun uu____9756  ->
           let uu____9757 = cur_goal ()  in
           bind uu____9757
             (fun g  ->
                let uu____9763 =
                  let uu____9772 = FStar_Tactics_Types.goal_env g  in
                  __tc uu____9772 ty  in
                bind uu____9763
                  (fun uu____9784  ->
                     match uu____9784 with
                     | (ty1,uu____9794,guard) ->
                         let uu____9796 =
                           let uu____9799 = FStar_Tactics_Types.goal_env g
                              in
                           proc_guard "change" uu____9799 guard
                             g.FStar_Tactics_Types.opts
                            in
                         bind uu____9796
                           (fun uu____9802  ->
                              let uu____9803 =
                                let uu____9806 =
                                  FStar_Tactics_Types.goal_env g  in
                                let uu____9807 =
                                  FStar_Tactics_Types.goal_type g  in
                                do_unify uu____9806 uu____9807 ty1  in
                              bind uu____9803
                                (fun bb  ->
                                   if bb
                                   then
                                     let uu____9813 =
                                       FStar_Tactics_Types.goal_with_type g
                                         ty1
                                        in
                                     replace_cur uu____9813
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
                                        let uu____9819 =
                                          FStar_Tactics_Types.goal_env g  in
                                        let uu____9820 =
                                          FStar_Tactics_Types.goal_type g  in
                                        normalize steps uu____9819 uu____9820
                                         in
                                      let nty =
                                        let uu____9822 =
                                          FStar_Tactics_Types.goal_env g  in
                                        normalize steps uu____9822 ty1  in
                                      let uu____9823 =
                                        let uu____9826 =
                                          FStar_Tactics_Types.goal_env g  in
                                        do_unify uu____9826 ng nty  in
                                      bind uu____9823
                                        (fun b  ->
                                           if b
                                           then
                                             let uu____9832 =
                                               FStar_Tactics_Types.goal_with_type
                                                 g ty1
                                                in
                                             replace_cur uu____9832
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9747
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9854::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9882 = init xs  in x :: uu____9882
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9894 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9902) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____9959 = last args  in
          (match uu____9959 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____9981 =
                 let uu____9982 =
                   let uu____9987 =
                     let uu____9988 =
                       let uu____9993 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9993  in
                     uu____9988 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____9987, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____9982  in
               FStar_All.pipe_left ret uu____9981)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____10004,uu____10005) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____10049 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____10049 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____10082 =
                      let uu____10083 =
                        let uu____10088 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____10088)  in
                      FStar_Reflection_Data.Tv_Abs uu____10083  in
                    FStar_All.pipe_left ret uu____10082))
      | FStar_Syntax_Syntax.Tm_type uu____10091 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____10111 ->
          let uu____10124 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____10124 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____10154 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____10154 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____10193 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____10201 =
            let uu____10202 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____10202  in
          FStar_All.pipe_left ret uu____10201
      | FStar_Syntax_Syntax.Tm_uvar (ctx_u,s) ->
          let uu____10227 =
            let uu____10228 =
              let uu____10233 =
                let uu____10234 =
                  FStar_Syntax_Unionfind.uvar_id
                    ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_BigInt.of_int_fs uu____10234  in
              (uu____10233, (ctx_u, s))  in
            FStar_Reflection_Data.Tv_Uvar uu____10228  in
          FStar_All.pipe_left ret uu____10227
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____10270 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____10275 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____10275 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____10314 ->
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
             | FStar_Util.Inr uu____10344 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____10348 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____10348 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____10368 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____10372 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____10426 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____10426
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____10445 =
                  let uu____10452 =
                    FStar_List.map
                      (fun uu____10464  ->
                         match uu____10464 with
                         | (p1,uu____10472) -> inspect_pat p1) ps
                     in
                  (fv, uu____10452)  in
                FStar_Reflection_Data.Pat_Cons uu____10445
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
              (fun uu___92_10556  ->
                 match uu___92_10556 with
                 | (pat,uu____10574,t4) ->
                     let uu____10588 = inspect_pat pat  in (uu____10588, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____10595 ->
          ((let uu____10597 =
              let uu____10602 =
                let uu____10603 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____10604 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n"
                  uu____10603 uu____10604
                 in
              (FStar_Errors.Warning_CantInspect, uu____10602)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____10597);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9894
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____10617 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____10617
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____10621 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____10621
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____10625 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____10625
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____10632 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____10632
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____10655 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____10655
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____10672 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____10672
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____10691 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____10691
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____10699 =
          let uu____10702 =
            let uu____10709 =
              let uu____10710 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____10710  in
            FStar_Syntax_Syntax.mk uu____10709  in
          uu____10702 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10699
    | FStar_Reflection_Data.Tv_Uvar (_u,ctx_u_s) ->
        let uu____10720 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10720
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10733 =
          let uu____10736 =
            let uu____10743 =
              let uu____10744 =
                let uu____10757 =
                  let uu____10760 =
                    let uu____10761 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10761]  in
                  FStar_Syntax_Subst.close uu____10760 t2  in
                ((false, [lb]), uu____10757)  in
              FStar_Syntax_Syntax.Tm_let uu____10744  in
            FStar_Syntax_Syntax.mk uu____10743  in
          uu____10736 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____10733
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10797 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10797 with
         | (lbs,body) ->
             let uu____10812 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10812)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10850 =
                let uu____10851 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10851  in
              FStar_All.pipe_left wrap uu____10850
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10858 =
                let uu____10859 =
                  let uu____10872 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10888 = pack_pat p1  in
                         (uu____10888, false)) ps
                     in
                  (fv, uu____10872)  in
                FStar_Syntax_Syntax.Pat_cons uu____10859  in
              FStar_All.pipe_left wrap uu____10858
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
            (fun uu___93_10934  ->
               match uu___93_10934 with
               | (pat,t1) ->
                   let uu____10951 = pack_pat pat  in
                   (uu____10951, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10999 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10999
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____11031 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11031
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____11081 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11081
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____11124 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____11124
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____11145 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____11145 with
      | (u,ctx_uvars,g_u) ->
          let uu____11177 = FStar_List.hd ctx_uvars  in
          (match uu____11177 with
           | (ctx_uvar,uu____11191) ->
               let g =
                 let uu____11193 = FStar_Options.peek ()  in
                 FStar_Tactics_Types.mk_goal env ctx_uvar uu____11193 false
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
        let uu____11213 = goal_of_goal_ty env typ  in
        match uu____11213 with
        | (g,g_u) ->
            let ps =
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
                FStar_Tactics_Types.freshness = (Prims.parse_int "0")
              }  in
            let uu____11229 = FStar_Tactics_Types.goal_witness g  in
            (ps, uu____11229)
  