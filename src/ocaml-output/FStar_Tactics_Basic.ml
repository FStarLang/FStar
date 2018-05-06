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
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let g_binders =
      let uu____247 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      FStar_All.pipe_right uu____247
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness
       in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
       in
    let uu____250 = tts g.FStar_Tactics_Types.context w  in
    let uu____251 = tts g.FStar_Tactics_Types.context t  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____250 uu____251
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____267 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____267
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____283 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____283
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____304 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____304
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____311) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____321) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____336 =
      let uu____341 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty
         in
      FStar_Syntax_Util.un_squash uu____341  in
    match uu____336 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____347 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____375 =
            let uu____376 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____376  in
          if uu____375 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____384 . 'Auu____384 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____396 = goal_to_string goal  in tacprint uu____396
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____408 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____412 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____412))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____421  ->
    match uu____421 with
    | (msg,ps) ->
        let uu____428 =
          let uu____431 =
            let uu____432 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____432 msg
             in
          let uu____433 =
            let uu____436 =
              let uu____437 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____437  in
            let uu____438 =
              let uu____441 =
                let uu____442 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____443 =
                  let uu____444 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____444  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____442
                  uu____443
                 in
              let uu____447 =
                let uu____450 =
                  let uu____451 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____452 =
                    let uu____453 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____453  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____451
                    uu____452
                   in
                [uu____450]  in
              uu____441 :: uu____447  in
            uu____436 :: uu____438  in
          uu____431 :: uu____433  in
        FStar_String.concat "" uu____428
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____462 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____463 =
        let uu____468 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____468  in
      FStar_All.pipe_right uu____462 uu____463  in
    let uu____469 =
      let uu____476 =
        let uu____483 =
          let uu____488 =
            let uu____489 =
              let uu____496 =
                let uu____501 =
                  let uu____502 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____502  in
                ("witness", uu____501)  in
              let uu____503 =
                let uu____510 =
                  let uu____515 =
                    let uu____516 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____516  in
                  ("type", uu____515)  in
                [uu____510]  in
              uu____496 :: uu____503  in
            FStar_Util.JsonAssoc uu____489  in
          ("goal", uu____488)  in
        [uu____483]  in
      ("hyps", g_binders) :: uu____476  in
    FStar_Util.JsonAssoc uu____469
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____549  ->
    match uu____549 with
    | (msg,ps) ->
        let uu____556 =
          let uu____563 =
            let uu____570 =
              let uu____577 =
                let uu____584 =
                  let uu____589 =
                    let uu____590 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____590  in
                  ("goals", uu____589)  in
                let uu____593 =
                  let uu____600 =
                    let uu____605 =
                      let uu____606 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____606  in
                    ("smt-goals", uu____605)  in
                  [uu____600]  in
                uu____584 :: uu____593  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____577
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____570  in
          let uu____629 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____642 =
                let uu____647 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____647)  in
              [uu____642]
            else []  in
          FStar_List.append uu____563 uu____629  in
        FStar_Util.JsonAssoc uu____556
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____677  ->
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
         (let uu____700 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____700 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____718 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____718 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____751 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____751 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____782 =
              let uu____785 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____785  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____782);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____866 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____866
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____874 . Prims.string -> Prims.string -> 'Auu____874 tac =
  fun msg  ->
    fun x  -> let uu____887 = FStar_Util.format1 msg x  in fail uu____887
  
let fail2 :
  'Auu____896 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____896 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____914 = FStar_Util.format2 msg x y  in fail uu____914
  
let fail3 :
  'Auu____925 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____925 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____948 = FStar_Util.format3 msg x y z  in fail uu____948
  
let fail4 :
  'Auu____961 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____961 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____989 = FStar_Util.format4 msg x y z w  in fail uu____989
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1022 = run t ps  in
         match uu____1022 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___91_1046 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___91_1046.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___91_1046.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___91_1046.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___91_1046.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___91_1046.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___91_1046.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___91_1046.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___91_1046.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___91_1046.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___91_1046.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1073 = trytac' t  in
    bind uu____1073
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1100 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1136 = trytac t  in run uu____1136 ps
         with
         | FStar_Errors.Err (uu____1152,msg) ->
             (log ps
                (fun uu____1156  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1161,msg,uu____1163) ->
             (log ps
                (fun uu____1166  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1199 = run t ps  in
           match uu____1199 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1218  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1239 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1239
         then
           let uu____1240 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1241 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1240
             uu____1241
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1253 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1253
            then
              let uu____1254 = FStar_Util.string_of_bool res  in
              let uu____1255 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1256 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1254 uu____1255 uu____1256
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1264,msg) ->
             mlog
               (fun uu____1267  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1269  -> ret false)
         | FStar_Errors.Error (uu____1270,msg,r) ->
             mlog
               (fun uu____1275  ->
                  let uu____1276 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1276) (fun uu____1278  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1301  ->
             (let uu____1303 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1303
              then
                (FStar_Options.push ();
                 (let uu____1305 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1307 =
                let uu____1310 = __do_unify env t1 t2  in
                bind uu____1310
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
              bind uu____1307
                (fun r  ->
                   (let uu____1326 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1326 then FStar_Options.pop () else ());
                   ret r)))
  
let (trysolve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> Prims.bool tac) =
  fun goal  ->
    fun solution  ->
      do_unify goal.FStar_Tactics_Types.context solution
        goal.FStar_Tactics_Types.witness
  
let (__dismiss : unit tac) =
  bind get
    (fun p  ->
       let uu____1347 =
         let uu___96_1348 = p  in
         let uu____1349 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___96_1348.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___96_1348.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___96_1348.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1349;
           FStar_Tactics_Types.smt_goals =
             (uu___96_1348.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___96_1348.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___96_1348.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___96_1348.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___96_1348.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___96_1348.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___96_1348.FStar_Tactics_Types.freshness)
         }  in
       set uu____1347)
  
let (dismiss : unit -> unit tac) =
  fun uu____1358  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1365 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = goal.FStar_Tactics_Types.context  in
      mlog
        (fun uu____1386  ->
           let uu____1387 = tts e goal.FStar_Tactics_Types.witness  in
           let uu____1388 = tts e solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1387 uu____1388)
        (fun uu____1391  ->
           let uu____1392 = trysolve goal solution  in
           bind uu____1392
             (fun b  ->
                if b
                then __dismiss
                else
                  (let uu____1400 =
                     let uu____1401 =
                       tts goal.FStar_Tactics_Types.context solution  in
                     let uu____1402 =
                       tts goal.FStar_Tactics_Types.context
                         goal.FStar_Tactics_Types.witness
                        in
                     let uu____1403 =
                       tts goal.FStar_Tactics_Types.context
                         goal.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1401 uu____1402 uu____1403
                      in
                   fail uu____1400)))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___97_1410 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___97_1410.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___97_1410.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___97_1410.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___97_1410.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___97_1410.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___97_1410.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___97_1410.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___97_1410.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___97_1410.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___97_1410.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1429 = FStar_Options.defensive ()  in
    if uu____1429
    then
      let b = true  in
      let env = g.FStar_Tactics_Types.context  in
      let b1 =
        b && (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.witness)
         in
      let b2 =
        b1 &&
          (FStar_TypeChecker_Env.closed env g.FStar_Tactics_Types.goal_ty)
         in
      let rec aux b3 e =
        let uu____1445 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1445 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1463 =
        (let uu____1466 = aux b2 env  in Prims.op_Negation uu____1466) &&
          (let uu____1468 = FStar_ST.op_Bang nwarn  in
           uu____1468 < (Prims.parse_int "5"))
         in
      (if uu____1463
       then
         ((let uu____1493 =
             let uu____1498 =
               let uu____1499 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1499
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1498)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1493);
          (let uu____1500 =
             let uu____1501 = FStar_ST.op_Bang nwarn  in
             uu____1501 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1500))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___98_1569 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_1569.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___98_1569.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___98_1569.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___98_1569.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_1569.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___98_1569.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___98_1569.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___98_1569.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___98_1569.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___98_1569.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___99_1589 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___99_1589.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___99_1589.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___99_1589.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___99_1589.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___99_1589.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___99_1589.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___99_1589.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___99_1589.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___99_1589.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___99_1589.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___100_1609 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_1609.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___100_1609.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___100_1609.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___100_1609.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___100_1609.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_1609.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_1609.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_1609.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_1609.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_1609.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___101_1629 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___101_1629.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___101_1629.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___101_1629.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___101_1629.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___101_1629.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___101_1629.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___101_1629.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___101_1629.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___101_1629.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___101_1629.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1640  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___102_1654 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_1654.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___102_1654.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___102_1654.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___102_1654.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___102_1654.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_1654.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_1654.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_1654.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_1654.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_1654.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1686 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1686 with
        | (u,uu____1702,g_u) ->
            let uu____1716 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1716 (fun uu____1720  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1726 = FStar_Syntax_Util.un_squash t  in
    match uu____1726 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1736 =
          let uu____1737 = FStar_Syntax_Subst.compress t'  in
          uu____1737.FStar_Syntax_Syntax.n  in
        (match uu____1736 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1741 -> false)
    | uu____1742 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1752 = FStar_Syntax_Util.un_squash t  in
    match uu____1752 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1762 =
          let uu____1763 = FStar_Syntax_Subst.compress t'  in
          uu____1763.FStar_Syntax_Syntax.n  in
        (match uu____1762 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1767 -> false)
    | uu____1768 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1779  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : unit -> unit tac) =
  fun uu____1796  ->
    let uu____1799 =
      let uu____1802 = cur_goal ()  in
      bind uu____1802
        (fun g  ->
           (let uu____1809 =
              let uu____1814 =
                let uu____1815 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1815
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1814)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1809);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1799
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1826  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___103_1836 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___103_1836.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___103_1836.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___103_1836.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___103_1836.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___103_1836.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___103_1836.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___103_1836.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___103_1836.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___103_1836.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___103_1836.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1837 = set ps1  in
         bind uu____1837
           (fun uu____1842  ->
              let uu____1843 = FStar_BigInt.of_int_fs n1  in ret uu____1843))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1850  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1858 = FStar_BigInt.of_int_fs n1  in ret uu____1858)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1871  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1879 = FStar_BigInt.of_int_fs n1  in ret uu____1879)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1892  ->
    let uu____1895 = cur_goal ()  in
    bind uu____1895 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1927 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1927 phi  in
          let uu____1928 = new_uvar reason env typ  in
          bind uu____1928
            (fun u  ->
               let goal =
                 {
                   FStar_Tactics_Types.context = env;
                   FStar_Tactics_Types.witness = u;
                   FStar_Tactics_Types.goal_ty = typ;
                   FStar_Tactics_Types.opts = opts;
                   FStar_Tactics_Types.is_guard = false
                 }  in
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
             (fun uu____1977  ->
                let uu____1978 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1978)
             (fun uu____1980  ->
                try
                  let uu____2000 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____2000
                with
                | FStar_Errors.Err (uu____2027,msg) ->
                    let uu____2029 = tts e t  in
                    let uu____2030 =
                      let uu____2031 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2031
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2029 uu____2030 msg
                | FStar_Errors.Error (uu____2038,msg,uu____2040) ->
                    let uu____2041 = tts e t  in
                    let uu____2042 =
                      let uu____2043 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2043
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2041 uu____2042 msg))
  
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
  fun uu____2070  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___106_2088 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___106_2088.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___106_2088.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___106_2088.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___106_2088.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___106_2088.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___106_2088.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___106_2088.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___106_2088.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___106_2088.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___106_2088.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2112 = get_guard_policy ()  in
      bind uu____2112
        (fun old_pol  ->
           let uu____2118 = set_guard_policy pol  in
           bind uu____2118
             (fun uu____2122  ->
                bind t
                  (fun r  ->
                     let uu____2126 = set_guard_policy old_pol  in
                     bind uu____2126 (fun uu____2130  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2155 =
            let uu____2156 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2156.FStar_TypeChecker_Env.guard_f  in
          match uu____2155 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2160 = istrivial e f  in
              if uu____2160
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2168 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2168
                           (fun goal  ->
                              let goal1 =
                                let uu___107_2175 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___107_2175.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___107_2175.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_2175.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_2175.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2176 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2176
                           (fun goal  ->
                              let goal1 =
                                let uu___108_2183 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___108_2183.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___108_2183.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_2183.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_2183.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2191 =
                              let uu____2192 =
                                let uu____2193 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2193
                                 in
                              Prims.op_Negation uu____2192  in
                            if uu____2191
                            then
                              mlog
                                (fun uu____2198  ->
                                   let uu____2199 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2199)
                                (fun uu____2201  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2208 ->
                              mlog
                                (fun uu____2211  ->
                                   let uu____2212 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2212)
                                (fun uu____2214  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2224 =
      let uu____2227 = cur_goal ()  in
      bind uu____2227
        (fun goal  ->
           let uu____2233 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2233
             (fun uu____2253  ->
                match uu____2253 with
                | (t1,typ,guard) ->
                    let uu____2265 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2265 (fun uu____2269  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2224
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2298 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2298 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2309  ->
    let uu____2312 = cur_goal ()  in
    bind uu____2312
      (fun goal  ->
         let uu____2318 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2318
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2322 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2322))
  
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
          let uu____2351 =
            let uu____2352 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2352.FStar_TypeChecker_Env.guard_f  in
          match uu____2351 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2360 = istrivial e f  in
              if uu____2360
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2368 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2368
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___111_2378 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___111_2378.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___111_2378.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___111_2378.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___111_2378.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2385  ->
    let uu____2388 = cur_goal ()  in
    bind uu____2388
      (fun g  ->
         let uu____2394 = is_irrelevant g  in
         if uu____2394
         then bind __dismiss (fun uu____2398  -> add_smt_goals [g])
         else
           (let uu____2400 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2400))
  
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
             let uu____2449 =
               try
                 let uu____2483 =
                   let uu____2492 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2492 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2483
               with | uu____2514 -> fail "divide: not enough goals"  in
             bind uu____2449
               (fun uu____2541  ->
                  match uu____2541 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___112_2567 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___112_2567.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___112_2567.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___112_2567.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___112_2567.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___112_2567.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___112_2567.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___112_2567.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___112_2567.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___112_2567.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___113_2569 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___113_2569.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___113_2569.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___113_2569.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___113_2569.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___113_2569.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___113_2569.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___113_2569.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___113_2569.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___113_2569.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2570 = set lp  in
                      bind uu____2570
                        (fun uu____2578  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2592 = set rp  in
                                     bind uu____2592
                                       (fun uu____2600  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___114_2616 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___114_2616.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___114_2616.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2617 = set p'
                                                       in
                                                    bind uu____2617
                                                      (fun uu____2625  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2646 = divide FStar_BigInt.one f idtac  in
    bind uu____2646
      (fun uu____2659  -> match uu____2659 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2696::uu____2697 ->
             let uu____2700 =
               let uu____2709 = map tau  in
               divide FStar_BigInt.one tau uu____2709  in
             bind uu____2700
               (fun uu____2727  ->
                  match uu____2727 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2768 =
        bind t1
          (fun uu____2773  ->
             let uu____2774 = map t2  in
             bind uu____2774 (fun uu____2782  -> ret ()))
         in
      focus uu____2768
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2791  ->
    let uu____2794 =
      let uu____2797 = cur_goal ()  in
      bind uu____2797
        (fun goal  ->
           let uu____2806 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2806 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2821 =
                 let uu____2822 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2822  in
               if uu____2821
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2828 = new_uvar "intro" env' typ'  in
                  bind uu____2828
                    (fun u  ->
                       let uu____2834 =
                         let uu____2837 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2837  in
                       bind uu____2834
                         (fun bb  ->
                            if bb
                            then
                              let uu____2843 =
                                let uu____2846 =
                                  let uu___117_2847 = goal  in
                                  let uu____2848 = bnorm env' u  in
                                  let uu____2849 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2848;
                                    FStar_Tactics_Types.goal_ty = uu____2849;
                                    FStar_Tactics_Types.opts =
                                      (uu___117_2847.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___117_2847.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2846  in
                              bind uu____2843 (fun uu____2851  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2857 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2857)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2794
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2872  ->
    let uu____2879 = cur_goal ()  in
    bind uu____2879
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2896 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2896 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2915 =
                let uu____2916 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2916  in
              if uu____2915
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2932 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2932; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2934 =
                   let uu____2937 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2937  in
                 bind uu____2934
                   (fun u  ->
                      let lb =
                        let uu____2952 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2952 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2958 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2958 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2988 = trysolve goal tm  in
                          bind uu____2988
                            (fun bb  ->
                               if bb
                               then
                                 let uu____3004 =
                                   let uu____3007 =
                                     let uu___118_3008 = goal  in
                                     let uu____3009 = bnorm env' u  in
                                     let uu____3010 =
                                       let uu____3011 = comp_to_typ c  in
                                       bnorm env' uu____3011  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____3009;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____3010;
                                       FStar_Tactics_Types.opts =
                                         (uu___118_3008.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___118_3008.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____3007  in
                                 bind uu____3004
                                   (fun uu____3018  ->
                                      let uu____3019 =
                                        let uu____3024 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____3024, b)  in
                                      ret uu____3019)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____3038 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3038))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3056 = cur_goal ()  in
    bind uu____3056
      (fun goal  ->
         mlog
           (fun uu____3063  ->
              let uu____3064 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3064)
           (fun uu____3069  ->
              let steps =
                let uu____3073 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3073
                 in
              let w =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.witness
                 in
              let t =
                normalize steps goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              replace_cur
                (let uu___119_3080 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_3080.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___119_3080.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___119_3080.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3104 =
          mlog
            (fun uu____3109  ->
               let uu____3110 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3110)
            (fun uu____3112  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3118 -> g.FStar_Tactics_Types.opts
                      | uu____3121 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3126  ->
                         let uu____3127 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3127)
                      (fun uu____3130  ->
                         let uu____3131 = __tc e t  in
                         bind uu____3131
                           (fun uu____3152  ->
                              match uu____3152 with
                              | (t1,uu____3162,uu____3163) ->
                                  let steps =
                                    let uu____3167 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3167
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3104
  
let (refine_intro : unit -> unit tac) =
  fun uu____3181  ->
    let uu____3184 =
      let uu____3187 = cur_goal ()  in
      bind uu____3187
        (fun g  ->
           let uu____3194 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3194 with
           | (uu____3207,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___120_3232 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___120_3232.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___120_3232.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___120_3232.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___120_3232.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3233 =
                 let uu____3238 =
                   let uu____3243 =
                     let uu____3244 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3244]  in
                   FStar_Syntax_Subst.open_term uu____3243 phi  in
                 match uu____3238 with
                 | (bvs,phi1) ->
                     let uu____3251 =
                       let uu____3252 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3252  in
                     (uu____3251, phi1)
                  in
               (match uu____3233 with
                | (bv1,phi1) ->
                    let uu____3265 =
                      let uu____3268 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3268
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3265
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3272  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3184
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3291 = cur_goal ()  in
      bind uu____3291
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3300 = __tc env t  in
           bind uu____3300
             (fun uu____3319  ->
                match uu____3319 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3334  ->
                         let uu____3335 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3336 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3335 uu____3336)
                      (fun uu____3339  ->
                         let uu____3340 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3340
                           (fun uu____3344  ->
                              mlog
                                (fun uu____3348  ->
                                   let uu____3349 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3350 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3349 uu____3350)
                                (fun uu____3353  ->
                                   let uu____3354 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3354
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3362 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3363 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3364 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3365 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3362 uu____3363 uu____3364
                                             uu____3365)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3380 =
        mlog
          (fun uu____3385  ->
             let uu____3386 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3386)
          (fun uu____3389  ->
             let uu____3390 =
               let uu____3397 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3397  in
             bind uu____3390
               (fun uu___84_3406  ->
                  match uu___84_3406 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3416  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3419  ->
                           let uu____3420 =
                             let uu____3427 =
                               let uu____3430 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3430
                                 (fun uu____3435  ->
                                    let uu____3436 = refine_intro ()  in
                                    bind uu____3436
                                      (fun uu____3440  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3427  in
                           bind uu____3420
                             (fun uu___83_3447  ->
                                match uu___83_3447 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3455 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3380
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3474 =
             let uu____3481 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3481  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3474  in
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
          let uu____3551 = f x  in
          bind uu____3551
            (fun y  ->
               let uu____3559 = mapM f xs  in
               bind uu____3559 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3579 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3599 = cur_goal ()  in
        bind uu____3599
          (fun goal  ->
             mlog
               (fun uu____3606  ->
                  let uu____3607 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3607)
               (fun uu____3610  ->
                  let uu____3611 =
                    let uu____3616 =
                      let uu____3619 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3619  in
                    trytac_exn uu____3616  in
                  bind uu____3611
                    (fun uu___85_3626  ->
                       match uu___85_3626 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3634  ->
                                let uu____3635 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3635)
                             (fun uu____3638  ->
                                let uu____3639 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3639 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3671  ->
                                         let uu____3672 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3672)
                                      (fun uu____3675  ->
                                         let uu____3676 =
                                           let uu____3677 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3677  in
                                         if uu____3676
                                         then fail "not total codomain"
                                         else
                                           (let uu____3681 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3681
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3701 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3701
                                                    in
                                                 let uu____3702 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3702
                                                   (fun uu____3710  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3712 =
                                                        let uu____3713 =
                                                          let uu____3716 =
                                                            let uu____3717 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3717
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3716
                                                           in
                                                        uu____3713.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3712 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3745)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3773
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3773
                                                               then ret ()
                                                               else
                                                                 (let uu____3777
                                                                    =
                                                                    let uu____3780
                                                                    =
                                                                    let uu___121_3781
                                                                    = goal
                                                                     in
                                                                    let uu____3782
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3783
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___121_3781.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3782;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3783;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___121_3781.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3780]
                                                                     in
                                                                  add_goals
                                                                    uu____3777))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3838 =
        mlog
          (fun uu____3843  ->
             let uu____3844 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3844)
          (fun uu____3847  ->
             let uu____3848 = cur_goal ()  in
             bind uu____3848
               (fun goal  ->
                  let uu____3854 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3854
                    (fun uu____3876  ->
                       match uu____3876 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3889 =
                             let uu____3892 =
                               let uu____3895 = __apply uopt tm1 typ1  in
                               bind uu____3895
                                 (fun uu____3899  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3892  in
                           let uu____3900 =
                             let uu____3903 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3904 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3905 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3903 uu____3904 uu____3905
                              in
                           try_unif uu____3889 uu____3900)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3838
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3928 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3928
    then
      let uu____3935 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3954 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3995 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3935 with
      | (pre,post) ->
          let post1 =
            let uu____4031 =
              let uu____4040 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4040]  in
            FStar_Syntax_Util.mk_app post uu____4031  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4054 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4054
       then
         let uu____4061 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4061
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4094 =
      let uu____4097 =
        mlog
          (fun uu____4102  ->
             let uu____4103 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4103)
          (fun uu____4107  ->
             let is_unit_t t =
               let uu____4114 =
                 let uu____4115 = FStar_Syntax_Subst.compress t  in
                 uu____4115.FStar_Syntax_Syntax.n  in
               match uu____4114 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4119 -> false  in
             let uu____4120 = cur_goal ()  in
             bind uu____4120
               (fun goal  ->
                  let uu____4126 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4126
                    (fun uu____4149  ->
                       match uu____4149 with
                       | (tm1,t,guard) ->
                           let uu____4161 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4161 with
                            | (bs,comp) ->
                                let uu____4188 = lemma_or_sq comp  in
                                (match uu____4188 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4207 =
                                       FStar_List.fold_left
                                         (fun uu____4249  ->
                                            fun uu____4250  ->
                                              match (uu____4249, uu____4250)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4341 =
                                                    is_unit_t b_t  in
                                                  if uu____4341
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4369 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4369 with
                                                     | (u,uu____4397,g_u) ->
                                                         let uu____4411 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4411,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4207 with
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
                                          let uu____4470 =
                                            let uu____4473 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4473
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4470
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4481 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4482 =
                                                   let uu____4483 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4483
                                                    in
                                                 let uu____4484 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4481 uu____4482
                                                   uu____4484
                                               else
                                                 (let uu____4486 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4486
                                                    (fun uu____4491  ->
                                                       let uu____4492 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4492
                                                         (fun uu____4500  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4515
                                                                  =
                                                                  let uu____4522
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4522
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4515
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
                                                                   is_free_uvar
                                                                    uv
                                                                    g'.FStar_Tactics_Types.goal_ty)
                                                                goals
                                                               in
                                                            let checkone t1
                                                              goals =
                                                              let uu____4571
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4571
                                                              with
                                                              | (hd1,uu____4587)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4609)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4634
                                                                    -> false)
                                                               in
                                                            let uu____4635 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4707
                                                                     ->
                                                                    match uu____4707
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4735)
                                                                    ->
                                                                    let uu____4736
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4736
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4762)
                                                                    ->
                                                                    let uu____4783
                                                                    =
                                                                    let uu____4784
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4784.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4783
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4797
                                                                    ->
                                                                    let uu____4814
                                                                    =
                                                                    let uu____4823
                                                                    =
                                                                    let uu____4826
                                                                    =
                                                                    let uu___124_4827
                                                                    = goal
                                                                     in
                                                                    let uu____4828
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4829
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___124_4827.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4828;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4829;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___124_4827.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___124_4827.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4826]
                                                                     in
                                                                    (uu____4823,
                                                                    [])  in
                                                                    ret
                                                                    uu____4814
                                                                    | 
                                                                    uu____4842
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4844
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4844
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4847
                                                                    =
                                                                    let uu____4854
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4854
                                                                    term1  in
                                                                    match uu____4847
                                                                    with
                                                                    | 
                                                                    (uu____4855,uu____4856,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4858
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4858
                                                                    (fun
                                                                    uu___86_4874
                                                                     ->
                                                                    match uu___86_4874
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
                                                            bind uu____4635
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4942
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4942
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4964
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4964
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5025
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5025
                                                                    then
                                                                    let uu____5028
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5028
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
                                                                    let uu____5042
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5042)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5043
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5043
                                                                   (fun
                                                                    uu____5048
                                                                     ->
                                                                    let uu____5049
                                                                    =
                                                                    let uu____5052
                                                                    =
                                                                    let uu____5053
                                                                    =
                                                                    let uu____5054
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5054
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5053
                                                                     in
                                                                    if
                                                                    uu____5052
                                                                    then
                                                                    add_irrelevant_goal
                                                                    "apply_lemma precondition"
                                                                    goal.FStar_Tactics_Types.context
                                                                    pre1
                                                                    goal.FStar_Tactics_Types.opts
                                                                    else
                                                                    ret ()
                                                                     in
                                                                    bind
                                                                    uu____5049
                                                                    (fun
                                                                    uu____5060
                                                                     ->
                                                                    let uu____5061
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5061
                                                                    (fun
                                                                    uu____5065
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4097  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4094
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5087 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5087 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5097::(e1,uu____5099)::(e2,uu____5101)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5160 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5184 = destruct_eq' typ  in
    match uu____5184 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5214 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5214 with
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
        let uu____5276 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5276 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5324 = aux e'  in
               FStar_Util.map_opt uu____5324
                 (fun uu____5348  ->
                    match uu____5348 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5369 = aux e  in
      FStar_Util.map_opt uu____5369
        (fun uu____5393  ->
           match uu____5393 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5460 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5460
            (fun uu____5484  ->
               match uu____5484 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___125_5503 = bv  in
                     let uu____5504 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___125_5503.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___125_5503.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5504
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___126_5513 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___126_5513.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___126_5513.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5523 =
      let uu____5526 = cur_goal ()  in
      bind uu____5526
        (fun goal  ->
           let uu____5534 = h  in
           match uu____5534 with
           | (bv,uu____5538) ->
               mlog
                 (fun uu____5542  ->
                    let uu____5543 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5544 =
                      tts goal.FStar_Tactics_Types.context
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5543
                      uu____5544)
                 (fun uu____5547  ->
                    let uu____5548 =
                      split_env bv goal.FStar_Tactics_Types.context  in
                    match uu____5548 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5577 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5577 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5592 =
                               let uu____5593 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5593.FStar_Syntax_Syntax.n  in
                             (match uu____5592 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___127_5608 = bv1  in
                                    let uu____5609 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___127_5608.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___127_5608.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5609
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let uu____5615 =
                                    let uu___128_5616 = goal  in
                                    let uu____5617 = push_bvs e0 (bv :: bvs1)
                                       in
                                    let uu____5618 =
                                      FStar_Syntax_Subst.subst s
                                        goal.FStar_Tactics_Types.witness
                                       in
                                    let uu____5619 =
                                      FStar_Syntax_Subst.subst s
                                        goal.FStar_Tactics_Types.goal_ty
                                       in
                                    {
                                      FStar_Tactics_Types.context =
                                        uu____5617;
                                      FStar_Tactics_Types.witness =
                                        uu____5618;
                                      FStar_Tactics_Types.goal_ty =
                                        uu____5619;
                                      FStar_Tactics_Types.opts =
                                        (uu___128_5616.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___128_5616.FStar_Tactics_Types.is_guard)
                                    }  in
                                  replace_cur uu____5615
                              | uu____5620 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5621 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5523
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5646 =
        let uu____5649 = cur_goal ()  in
        bind uu____5649
          (fun goal  ->
             let uu____5660 = b  in
             match uu____5660 with
             | (bv,uu____5664) ->
                 let bv' =
                   let uu____5666 =
                     let uu___129_5667 = bv  in
                     let uu____5668 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____5668;
                       FStar_Syntax_Syntax.index =
                         (uu___129_5667.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___129_5667.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____5666  in
                 let s1 =
                   let uu____5672 =
                     let uu____5673 =
                       let uu____5680 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____5680)  in
                     FStar_Syntax_Syntax.NT uu____5673  in
                   [uu____5672]  in
                 let uu____5681 = subst_goal bv bv' s1 goal  in
                 (match uu____5681 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____5646
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5700 =
      let uu____5703 = cur_goal ()  in
      bind uu____5703
        (fun goal  ->
           let uu____5712 = b  in
           match uu____5712 with
           | (bv,uu____5716) ->
               let uu____5717 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5717 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____5746 = FStar_Syntax_Util.type_u ()  in
                    (match uu____5746 with
                     | (ty,u) ->
                         let uu____5755 = new_uvar "binder_retype" e0 ty  in
                         bind uu____5755
                           (fun t'  ->
                              let bv'' =
                                let uu___130_5765 = bv  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_5765.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_5765.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t'
                                }  in
                              let s =
                                let uu____5769 =
                                  let uu____5770 =
                                    let uu____5777 =
                                      FStar_Syntax_Syntax.bv_to_name bv''  in
                                    (bv, uu____5777)  in
                                  FStar_Syntax_Syntax.NT uu____5770  in
                                [uu____5769]  in
                              let bvs1 =
                                FStar_List.map
                                  (fun b1  ->
                                     let uu___131_5785 = b1  in
                                     let uu____5786 =
                                       FStar_Syntax_Subst.subst s
                                         b1.FStar_Syntax_Syntax.sort
                                        in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___131_5785.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___131_5785.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort = uu____5786
                                     }) bvs
                                 in
                              let env' = push_bvs e0 (bv'' :: bvs1)  in
                              bind __dismiss
                                (fun uu____5792  ->
                                   let uu____5793 =
                                     let uu____5796 =
                                       let uu____5799 =
                                         let uu___132_5800 = goal  in
                                         let uu____5801 =
                                           FStar_Syntax_Subst.subst s
                                             goal.FStar_Tactics_Types.witness
                                            in
                                         let uu____5802 =
                                           FStar_Syntax_Subst.subst s
                                             goal.FStar_Tactics_Types.goal_ty
                                            in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness =
                                             uu____5801;
                                           FStar_Tactics_Types.goal_ty =
                                             uu____5802;
                                           FStar_Tactics_Types.opts =
                                             (uu___132_5800.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___132_5800.FStar_Tactics_Types.is_guard)
                                         }  in
                                       [uu____5799]  in
                                     add_goals uu____5796  in
                                   bind uu____5793
                                     (fun uu____5805  ->
                                        let uu____5806 =
                                          FStar_Syntax_Util.mk_eq2
                                            (FStar_Syntax_Syntax.U_succ u) ty
                                            bv.FStar_Syntax_Syntax.sort t'
                                           in
                                        add_irrelevant_goal
                                          "binder_retype equation" e0
                                          uu____5806
                                          goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____5700
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5829 =
        let uu____5832 = cur_goal ()  in
        bind uu____5832
          (fun goal  ->
             let uu____5841 = b  in
             match uu____5841 with
             | (bv,uu____5845) ->
                 let uu____5846 =
                   split_env bv goal.FStar_Tactics_Types.context  in
                 (match uu____5846 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____5878 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____5878
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___133_5883 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___133_5883.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___133_5883.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      replace_cur
                        (let uu___134_5887 = goal  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness =
                             (uu___134_5887.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___134_5887.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___134_5887.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___134_5887.FStar_Tactics_Types.is_guard)
                         })))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____5829
  
let (revert : unit -> unit tac) =
  fun uu____5898  ->
    let uu____5901 = cur_goal ()  in
    bind uu____5901
      (fun goal  ->
         let uu____5907 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5907 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5929 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5929
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___135_5963 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___135_5963.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___135_5963.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5974 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5974
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5987 = cur_goal ()  in
    bind uu____5987
      (fun goal  ->
         mlog
           (fun uu____5995  ->
              let uu____5996 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5997 =
                let uu____5998 =
                  let uu____5999 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5999 FStar_List.length  in
                FStar_All.pipe_right uu____5998 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5996 uu____5997)
           (fun uu____6010  ->
              let uu____6011 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____6011 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6058 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6058
                        then
                          let uu____6061 =
                            let uu____6062 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6062
                             in
                          fail uu____6061
                        else check1 bvs2
                     in
                  let uu____6064 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____6064
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6068 = check1 bvs  in
                     bind uu____6068
                       (fun uu____6074  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6076 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6076
                            (fun ut  ->
                               let uu____6082 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6082
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___136_6091 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___136_6091.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___136_6091.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___136_6091.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6099  ->
    let uu____6102 = cur_goal ()  in
    bind uu____6102
      (fun goal  ->
         let uu____6108 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6108 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6122) ->
             let uu____6127 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6127)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6137 = cur_goal ()  in
    bind uu____6137
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6147 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6147  in
         let g' =
           let uu___137_6149 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___137_6149.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___137_6149.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___137_6149.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___137_6149.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6151  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6161 = cur_goal ()  in
    bind uu____6161
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6171 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6171  in
         let g' =
           let uu___138_6173 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___138_6173.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___138_6173.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___138_6173.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___138_6173.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6175  -> add_goals [g']))
  
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
            let uu____6215 = FStar_Syntax_Subst.compress t  in
            uu____6215.FStar_Syntax_Syntax.n  in
          let uu____6218 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___142_6224 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___142_6224.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___142_6224.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6218
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6240 =
                   let uu____6241 = FStar_Syntax_Subst.compress t1  in
                   uu____6241.FStar_Syntax_Syntax.n  in
                 match uu____6240 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6268 = ff hd1  in
                     bind uu____6268
                       (fun hd2  ->
                          let fa uu____6290 =
                            match uu____6290 with
                            | (a,q) ->
                                let uu____6303 = ff a  in
                                bind uu____6303 (fun a1  -> ret (a1, q))
                             in
                          let uu____6316 = mapM fa args  in
                          bind uu____6316
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6376 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6376 with
                      | (bs1,t') ->
                          let uu____6385 =
                            let uu____6388 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6388 t'  in
                          bind uu____6385
                            (fun t''  ->
                               let uu____6392 =
                                 let uu____6393 =
                                   let uu____6410 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6411 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6410, uu____6411, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6393  in
                               ret uu____6392))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6470 = ff hd1  in
                     bind uu____6470
                       (fun hd2  ->
                          let ffb br =
                            let uu____6485 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6485 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6517 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6517  in
                                let uu____6518 = ff1 e  in
                                bind uu____6518
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6531 = mapM ffb brs  in
                          bind uu____6531
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6545;
                          FStar_Syntax_Syntax.lbtyp = uu____6546;
                          FStar_Syntax_Syntax.lbeff = uu____6547;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6549;
                          FStar_Syntax_Syntax.lbpos = uu____6550;_}::[]),e)
                     ->
                     let lb =
                       let uu____6575 =
                         let uu____6576 = FStar_Syntax_Subst.compress t1  in
                         uu____6576.FStar_Syntax_Syntax.n  in
                       match uu____6575 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6580) -> lb
                       | uu____6593 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6602 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6602
                         (fun def1  ->
                            ret
                              (let uu___139_6608 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___139_6608.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___139_6608.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___139_6608.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___139_6608.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___139_6608.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___139_6608.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6609 = fflb lb  in
                     bind uu____6609
                       (fun lb1  ->
                          let uu____6619 =
                            let uu____6624 =
                              let uu____6625 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6625]  in
                            FStar_Syntax_Subst.open_term uu____6624 e  in
                          match uu____6619 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6637 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6637  in
                              let uu____6638 = ff1 e1  in
                              bind uu____6638
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6677 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6677
                         (fun def  ->
                            ret
                              (let uu___140_6683 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___140_6683.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___140_6683.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___140_6683.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___140_6683.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___140_6683.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___140_6683.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6684 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6684 with
                      | (lbs1,e1) ->
                          let uu____6699 = mapM fflb lbs1  in
                          bind uu____6699
                            (fun lbs2  ->
                               let uu____6711 = ff e1  in
                               bind uu____6711
                                 (fun e2  ->
                                    let uu____6719 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6719 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6785 = ff t2  in
                     bind uu____6785
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6814 = ff t2  in
                     bind uu____6814
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6819 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___141_6826 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___141_6826.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___141_6826.FStar_Syntax_Syntax.vars)
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
            let uu____6865 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6865 with
            | (t1,lcomp,g) ->
                let uu____6877 =
                  (let uu____6880 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6880) ||
                    (let uu____6882 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6882)
                   in
                if uu____6877
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6890 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6890
                       (fun ut  ->
                          log ps
                            (fun uu____6901  ->
                               let uu____6902 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6903 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6902 uu____6903);
                          (let uu____6904 =
                             let uu____6907 =
                               let uu____6908 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6908 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6907 opts
                              in
                           bind uu____6904
                             (fun uu____6911  ->
                                let uu____6912 =
                                  bind tau
                                    (fun uu____6918  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6924  ->
                                            let uu____6925 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6926 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6925 uu____6926);
                                       ret ut1)
                                   in
                                focus uu____6912)))
                      in
                   let uu____6927 = trytac' rewrite_eq  in
                   bind uu____6927
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
          let uu____7099 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7099
            (fun t1  ->
               let uu____7103 =
                 f env
                   (let uu___145_7112 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___145_7112.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___145_7112.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7103
                 (fun uu____7124  ->
                    match uu____7124 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7143 =
                               let uu____7144 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7144.FStar_Syntax_Syntax.n  in
                             match uu____7143 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7177 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7177
                                   (fun uu____7202  ->
                                      match uu____7202 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7218 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7218
                                            (fun uu____7245  ->
                                               match uu____7245 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___143_7275 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___143_7275.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___143_7275.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7301 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7301 with
                                  | (bs1,t') ->
                                      let uu____7316 =
                                        let uu____7323 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7323 ctrl1 t'
                                         in
                                      bind uu____7316
                                        (fun uu____7341  ->
                                           match uu____7341 with
                                           | (t'',ctrl2) ->
                                               let uu____7356 =
                                                 let uu____7363 =
                                                   let uu___144_7366 = t4  in
                                                   let uu____7369 =
                                                     let uu____7370 =
                                                       let uu____7387 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7388 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7387,
                                                         uu____7388, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7370
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7369;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___144_7366.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___144_7366.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7363, ctrl2)  in
                                               ret uu____7356))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7421 -> ret (t3, ctrl1))))

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
              let uu____7472 = ctrl_tac_fold f env ctrl t  in
              bind uu____7472
                (fun uu____7500  ->
                   match uu____7500 with
                   | (t1,ctrl1) ->
                       let uu____7519 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7519
                         (fun uu____7550  ->
                            match uu____7550 with
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
              let uu____7646 =
                let uu____7653 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7653
                  (fun uu____7662  ->
                     let uu____7663 = ctrl t1  in
                     bind uu____7663
                       (fun res  ->
                          let uu____7686 = trivial ()  in
                          bind uu____7686 (fun uu____7694  -> ret res)))
                 in
              bind uu____7646
                (fun uu____7710  ->
                   match uu____7710 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7734 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7734 with
                          | (t2,lcomp,g) ->
                              let uu____7750 =
                                (let uu____7753 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7753) ||
                                  (let uu____7755 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7755)
                                 in
                              if uu____7750
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7768 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7768
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7783  ->
                                           let uu____7784 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7785 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7784 uu____7785);
                                      (let uu____7786 =
                                         let uu____7789 =
                                           let uu____7790 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7790 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7789 opts
                                          in
                                       bind uu____7786
                                         (fun uu____7797  ->
                                            let uu____7798 =
                                              bind rewriter
                                                (fun uu____7812  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7818  ->
                                                        let uu____7819 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7820 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7819
                                                          uu____7820);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7798))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____7861 =
        bind get
          (fun ps  ->
             let uu____7871 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____7871 with
             | (g,gs) ->
                 let gt1 = g.FStar_Tactics_Types.goal_ty  in
                 (log ps
                    (fun uu____7908  ->
                       let uu____7909 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____7909);
                  bind dismiss_all
                    (fun uu____7912  ->
                       let uu____7913 =
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts)
                           g.FStar_Tactics_Types.context keepGoing gt1
                          in
                       bind uu____7913
                         (fun uu____7931  ->
                            match uu____7931 with
                            | (gt',uu____7939) ->
                                (log ps
                                   (fun uu____7943  ->
                                      let uu____7944 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____7944);
                                 (let uu____7945 = push_goals gs  in
                                  bind uu____7945
                                    (fun uu____7949  ->
                                       add_goals
                                         [(let uu___146_7951 = g  in
                                           {
                                             FStar_Tactics_Types.context =
                                               (uu___146_7951.FStar_Tactics_Types.context);
                                             FStar_Tactics_Types.witness =
                                               (uu___146_7951.FStar_Tactics_Types.witness);
                                             FStar_Tactics_Types.goal_ty =
                                               gt';
                                             FStar_Tactics_Types.opts =
                                               (uu___146_7951.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___146_7951.FStar_Tactics_Types.is_guard)
                                           })])))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____7861
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____7974 =
        bind get
          (fun ps  ->
             let uu____7984 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____7984 with
             | (g,gs) ->
                 let gt1 = g.FStar_Tactics_Types.goal_ty  in
                 (log ps
                    (fun uu____8021  ->
                       let uu____8022 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8022);
                  bind dismiss_all
                    (fun uu____8025  ->
                       let uu____8026 =
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           g.FStar_Tactics_Types.context gt1
                          in
                       bind uu____8026
                         (fun gt'  ->
                            log ps
                              (fun uu____8036  ->
                                 let uu____8037 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8037);
                            (let uu____8038 = push_goals gs  in
                             bind uu____8038
                               (fun uu____8042  ->
                                  add_goals
                                    [(let uu___147_8044 = g  in
                                      {
                                        FStar_Tactics_Types.context =
                                          (uu___147_8044.FStar_Tactics_Types.context);
                                        FStar_Tactics_Types.witness =
                                          (uu___147_8044.FStar_Tactics_Types.witness);
                                        FStar_Tactics_Types.goal_ty = gt';
                                        FStar_Tactics_Types.opts =
                                          (uu___147_8044.FStar_Tactics_Types.opts);
                                        FStar_Tactics_Types.is_guard =
                                          (uu___147_8044.FStar_Tactics_Types.is_guard)
                                      })]))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____7974
  
let (trefl : unit -> unit tac) =
  fun uu____8055  ->
    let uu____8058 =
      let uu____8061 = cur_goal ()  in
      bind uu____8061
        (fun g  ->
           let uu____8079 =
             FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
           match uu____8079 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8091 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8091 with
                | (hd1,args) ->
                    let uu____8124 =
                      let uu____8137 =
                        let uu____8138 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8138.FStar_Syntax_Syntax.n  in
                      (uu____8137, args)  in
                    (match uu____8124 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8152::(l,uu____8154)::(r,uu____8156)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8203 =
                           do_unify g.FStar_Tactics_Types.context l r  in
                         bind uu____8203
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8212 =
                                  tts g.FStar_Tactics_Types.context l  in
                                let uu____8213 =
                                  tts g.FStar_Tactics_Types.context r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8212 uu____8213
                              else solve g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8216) ->
                         let uu____8233 = tts g.FStar_Tactics_Types.context t
                            in
                         fail1 "not an equality (%s)" uu____8233))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8058
  
let (dup : unit -> unit tac) =
  fun uu____8246  ->
    let uu____8249 = cur_goal ()  in
    bind uu____8249
      (fun g  ->
         let uu____8255 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8255
           (fun u  ->
              let g' =
                let uu___148_8262 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___148_8262.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___148_8262.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___148_8262.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___148_8262.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8265  ->
                   let uu____8266 =
                     let uu____8269 =
                       let uu____8270 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8270
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8269
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8266
                     (fun uu____8273  ->
                        let uu____8274 = add_goals [g']  in
                        bind uu____8274 (fun uu____8278  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8285  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___149_8302 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___149_8302.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___149_8302.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___149_8302.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___149_8302.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___149_8302.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___149_8302.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___149_8302.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___149_8302.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___149_8302.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___149_8302.FStar_Tactics_Types.freshness)
                })
         | uu____8303 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8312  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___150_8325 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___150_8325.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___150_8325.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___150_8325.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___150_8325.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___150_8325.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___150_8325.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___150_8325.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___150_8325.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___150_8325.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___150_8325.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8332  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8339 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8359 =
      let uu____8366 = cur_goal ()  in
      bind uu____8366
        (fun g  ->
           let uu____8376 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8376
             (fun uu____8412  ->
                match uu____8412 with
                | (t1,typ,guard) ->
                    let uu____8428 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8428 with
                     | (hd1,args) ->
                         let uu____8471 =
                           let uu____8484 =
                             let uu____8485 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8485.FStar_Syntax_Syntax.n  in
                           (uu____8484, args)  in
                         (match uu____8471 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8504)::(q,uu____8506)::[]) when
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
                                let uu___151_8544 = g  in
                                let uu____8545 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8545;
                                  FStar_Tactics_Types.witness =
                                    (uu___151_8544.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___151_8544.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___151_8544.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___151_8544.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___152_8547 = g  in
                                let uu____8548 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8548;
                                  FStar_Tactics_Types.witness =
                                    (uu___152_8547.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___152_8547.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___152_8547.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___152_8547.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8555  ->
                                   let uu____8556 = add_goals [g1; g2]  in
                                   bind uu____8556
                                     (fun uu____8565  ->
                                        let uu____8566 =
                                          let uu____8571 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8572 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8571, uu____8572)  in
                                        ret uu____8566))
                          | uu____8577 ->
                              let uu____8590 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8590))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8359
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8620 =
      let uu____8623 = cur_goal ()  in
      bind uu____8623
        (fun g  ->
           FStar_Options.push ();
           (let uu____8636 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____8636);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___153_8643 = g  in
                   {
                     FStar_Tactics_Types.context =
                       (uu___153_8643.FStar_Tactics_Types.context);
                     FStar_Tactics_Types.witness =
                       (uu___153_8643.FStar_Tactics_Types.witness);
                     FStar_Tactics_Types.goal_ty =
                       (uu___153_8643.FStar_Tactics_Types.goal_ty);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___153_8643.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____8620
  
let (top_env : unit -> env tac) =
  fun uu____8655  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8668  ->
    let uu____8671 = cur_goal ()  in
    bind uu____8671
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8684  ->
    let uu____8687 = cur_goal ()  in
    bind uu____8687
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8700  ->
    let uu____8703 = cur_goal ()  in
    bind uu____8703
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8724 =
        let uu____8727 = cur_goal ()  in
        bind uu____8727
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8735 = __tc env tm  in
             bind uu____8735
               (fun uu____8755  ->
                  match uu____8755 with
                  | (tm1,typ,guard) ->
                      let uu____8767 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8767 (fun uu____8771  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8724
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8794 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8800 =
              let uu____8801 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8801  in
            new_uvar "uvar_env.2" env uu____8800
         in
      bind uu____8794
        (fun typ  ->
           let uu____8813 = new_uvar "uvar_env" env typ  in
           bind uu____8813 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8827 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8844 -> g.FStar_Tactics_Types.opts
             | uu____8847 -> FStar_Options.peek ()  in
           let uu____8850 = FStar_Syntax_Util.head_and_args t  in
           match uu____8850 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8867,typ);
                FStar_Syntax_Syntax.pos = uu____8869;
                FStar_Syntax_Syntax.vars = uu____8870;_},uu____8871)
               ->
               let uu____8916 =
                 let uu____8919 =
                   let uu____8920 = bnorm env t  in
                   let uu____8921 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8920;
                     FStar_Tactics_Types.goal_ty = uu____8921;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8919]  in
               add_goals uu____8916
           | uu____8922 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8827
  
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
          (fun uu____8983  ->
             let uu____8984 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8984
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
        (fun uu____9005  ->
           let uu____9006 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9006)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9016 =
      mlog
        (fun uu____9021  ->
           let uu____9022 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9022)
        (fun uu____9025  ->
           let uu____9026 = cur_goal ()  in
           bind uu____9026
             (fun g  ->
                let uu____9032 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____9032
                  (fun uu____9052  ->
                     match uu____9052 with
                     | (ty1,uu____9062,guard) ->
                         let uu____9064 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____9064
                           (fun uu____9069  ->
                              let uu____9070 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____9070
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___154_9079 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___154_9079.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___154_9079.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___154_9079.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___154_9079.FStar_Tactics_Types.is_guard)
                                        })
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
                                        normalize steps
                                          g.FStar_Tactics_Types.context
                                          g.FStar_Tactics_Types.goal_ty
                                         in
                                      let nty =
                                        normalize steps
                                          g.FStar_Tactics_Types.context ty1
                                         in
                                      let uu____9086 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____9086
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___155_9095 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___155_9095.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___155_9095.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___155_9095.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___155_9095.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9016
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9117::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9145 = init xs  in x :: uu____9145
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9157 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9165) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____9222 = last args  in
          (match uu____9222 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____9244 =
                 let uu____9245 =
                   let uu____9250 =
                     let uu____9253 =
                       let uu____9258 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9258  in
                     uu____9253 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____9250, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____9245  in
               FStar_All.pipe_left ret uu____9244)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____9279,uu____9280) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____9324 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____9324 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____9357 =
                      let uu____9358 =
                        let uu____9363 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____9363)  in
                      FStar_Reflection_Data.Tv_Abs uu____9358  in
                    FStar_All.pipe_left ret uu____9357))
      | FStar_Syntax_Syntax.Tm_type uu____9370 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____9390 ->
          let uu____9403 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____9403 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____9433 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____9433 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____9464 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____9472 =
            let uu____9473 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____9473  in
          FStar_All.pipe_left ret uu____9472
      | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
          let uu____9502 =
            let uu____9503 =
              let uu____9508 =
                let uu____9509 = FStar_Syntax_Unionfind.uvar_id u  in
                FStar_BigInt.of_int_fs uu____9509  in
              (uu____9508, t3)  in
            FStar_Reflection_Data.Tv_Uvar uu____9503  in
          FStar_All.pipe_left ret uu____9502
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____9537 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____9542 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____9542 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____9573 ->
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
             | FStar_Util.Inr uu____9605 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____9609 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____9609 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____9629 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____9635 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____9689 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____9689
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____9708 =
                  let uu____9715 =
                    FStar_List.map
                      (fun uu____9727  ->
                         match uu____9727 with
                         | (p1,uu____9735) -> inspect_pat p1) ps
                     in
                  (fv, uu____9715)  in
                FStar_Reflection_Data.Pat_Cons uu____9708
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
              (fun uu___87_9789  ->
                 match uu___87_9789 with
                 | (pat,uu____9811,t4) ->
                     let uu____9829 = inspect_pat pat  in (uu____9829, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____9846 ->
          ((let uu____9848 =
              let uu____9853 =
                let uu____9854 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____9855 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n" uu____9854
                  uu____9855
                 in
              (FStar_Errors.Warning_CantInspect, uu____9853)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9848);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9157
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9868 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9868
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9872 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9872
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9876 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9876
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9887 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9887
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9908 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9908
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9913 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9913
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9928 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9928
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9940 =
          let uu____9943 =
            let uu____9950 =
              let uu____9951 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9951  in
            FStar_Syntax_Syntax.mk uu____9950  in
          uu____9943 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9940
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9965 =
          let uu____9968 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9968 t  in
        FStar_All.pipe_left ret uu____9965
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9983 =
          let uu____9986 =
            let uu____9993 =
              let uu____9994 =
                let uu____10007 =
                  let uu____10008 =
                    let uu____10009 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10009]  in
                  FStar_Syntax_Subst.close uu____10008 t2  in
                ((false, [lb]), uu____10007)  in
              FStar_Syntax_Syntax.Tm_let uu____9994  in
            FStar_Syntax_Syntax.mk uu____9993  in
          uu____9986 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9983
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10035 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10035 with
         | (lbs,body) ->
             let uu____10050 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10050)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10090 =
                let uu____10091 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10091  in
              FStar_All.pipe_left wrap uu____10090
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10100 =
                let uu____10101 =
                  let uu____10114 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10128 = pack_pat p1  in
                         (uu____10128, false)) ps
                     in
                  (fv, uu____10114)  in
                FStar_Syntax_Syntax.Pat_cons uu____10101  in
              FStar_All.pipe_left wrap uu____10100
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
            (fun uu___88_10178  ->
               match uu___88_10178 with
               | (pat,t1) ->
                   let uu____10195 = pack_pat pat  in
                   (uu____10195, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10205 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10205
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10225 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10225
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10267 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10267
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10302 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10302
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10331 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10331 with
      | (u,uu____10349,g_u) ->
          let g =
            let uu____10364 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10364;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
let (proofstate_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.proofstate,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10379 = goal_of_goal_ty env typ  in
      match uu____10379 with
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
              FStar_Tactics_Types.psc = FStar_TypeChecker_Normalize.null_psc;
              FStar_Tactics_Types.entry_range = FStar_Range.dummyRange;
              FStar_Tactics_Types.guard_policy = FStar_Tactics_Types.SMT;
              FStar_Tactics_Types.freshness = (Prims.parse_int "0")
            }  in
          (ps, (g.FStar_Tactics_Types.witness))
  