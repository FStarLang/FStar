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
              if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
              then
                let uu____437 =
                  FStar_Range.string_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                FStar_Util.format1 "Location: %s\n" uu____437
              else ""  in
            let uu____439 =
              let uu____442 =
                let uu____443 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____444 =
                  let uu____445 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____445  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____443
                  uu____444
                 in
              let uu____448 =
                let uu____451 =
                  let uu____452 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____453 =
                    let uu____454 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____454  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____452
                    uu____453
                   in
                [uu____451]  in
              uu____442 :: uu____448  in
            uu____436 :: uu____439  in
          uu____431 :: uu____433  in
        FStar_String.concat "" uu____428
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____463 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____464 =
        let uu____469 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____469  in
      FStar_All.pipe_right uu____463 uu____464  in
    let uu____470 =
      let uu____477 =
        let uu____484 =
          let uu____489 =
            let uu____490 =
              let uu____497 =
                let uu____502 =
                  let uu____503 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____503  in
                ("witness", uu____502)  in
              let uu____504 =
                let uu____511 =
                  let uu____516 =
                    let uu____517 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____517  in
                  ("type", uu____516)  in
                [uu____511]  in
              uu____497 :: uu____504  in
            FStar_Util.JsonAssoc uu____490  in
          ("goal", uu____489)  in
        [uu____484]  in
      ("hyps", g_binders) :: uu____477  in
    FStar_Util.JsonAssoc uu____470
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____550  ->
    match uu____550 with
    | (msg,ps) ->
        let uu____557 =
          let uu____564 =
            let uu____571 =
              let uu____578 =
                let uu____585 =
                  let uu____590 =
                    let uu____591 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____591  in
                  ("goals", uu____590)  in
                let uu____594 =
                  let uu____601 =
                    let uu____606 =
                      let uu____607 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____607  in
                    ("smt-goals", uu____606)  in
                  [uu____601]  in
                uu____585 :: uu____594  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____578
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____571  in
          let uu____630 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____643 =
                let uu____648 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____648)  in
              [uu____643]
            else []  in
          FStar_List.append uu____564 uu____630  in
        FStar_Util.JsonAssoc uu____557
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____678  ->
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
         (let uu____701 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____701 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____719 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____719 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____752 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____752 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____783 =
              let uu____786 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____786  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____783);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____867 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____867
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____875 . Prims.string -> Prims.string -> 'Auu____875 tac =
  fun msg  ->
    fun x  -> let uu____888 = FStar_Util.format1 msg x  in fail uu____888
  
let fail2 :
  'Auu____897 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____897 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____915 = FStar_Util.format2 msg x y  in fail uu____915
  
let fail3 :
  'Auu____926 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____926 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____949 = FStar_Util.format3 msg x y z  in fail uu____949
  
let fail4 :
  'Auu____962 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____962 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____990 = FStar_Util.format4 msg x y z w  in fail uu____990
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____1023 = run t ps  in
         match uu____1023 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___91_1047 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___91_1047.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___91_1047.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___91_1047.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___91_1047.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___91_1047.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___91_1047.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___91_1047.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___91_1047.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___91_1047.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___91_1047.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1074 = trytac' t  in
    bind uu____1074
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1101 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1137 = trytac t  in run uu____1137 ps
         with
         | FStar_Errors.Err (uu____1153,msg) ->
             (log ps
                (fun uu____1157  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1162,msg,uu____1164) ->
             (log ps
                (fun uu____1167  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1200 = run t ps  in
           match uu____1200 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1219  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1240 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1240
         then
           let uu____1241 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1242 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1241
             uu____1242
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1254 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1254
            then
              let uu____1255 = FStar_Util.string_of_bool res  in
              let uu____1256 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1257 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1255 uu____1256 uu____1257
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1265,msg) ->
             mlog
               (fun uu____1268  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1270  -> ret false)
         | FStar_Errors.Error (uu____1271,msg,r) ->
             mlog
               (fun uu____1276  ->
                  let uu____1277 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1277) (fun uu____1279  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1302  ->
             (let uu____1304 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1304
              then
                (FStar_Options.push ();
                 (let uu____1306 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1308 =
                let uu____1311 = __do_unify env t1 t2  in
                bind uu____1311
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
              bind uu____1308
                (fun r  ->
                   (let uu____1327 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1327 then FStar_Options.pop () else ());
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
       let uu____1348 =
         let uu___96_1349 = p  in
         let uu____1350 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___96_1349.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___96_1349.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___96_1349.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1350;
           FStar_Tactics_Types.smt_goals =
             (uu___96_1349.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___96_1349.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___96_1349.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___96_1349.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___96_1349.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___96_1349.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___96_1349.FStar_Tactics_Types.freshness)
         }  in
       set uu____1348)
  
let (dismiss : unit -> unit tac) =
  fun uu____1359  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1366 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = goal.FStar_Tactics_Types.context  in
      mlog
        (fun uu____1387  ->
           let uu____1388 = tts e goal.FStar_Tactics_Types.witness  in
           let uu____1389 = tts e solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1388 uu____1389)
        (fun uu____1392  ->
           let uu____1393 = trysolve goal solution  in
           bind uu____1393
             (fun b  ->
                if b
                then __dismiss
                else
                  (let uu____1401 =
                     let uu____1402 =
                       tts goal.FStar_Tactics_Types.context solution  in
                     let uu____1403 =
                       tts goal.FStar_Tactics_Types.context
                         goal.FStar_Tactics_Types.witness
                        in
                     let uu____1404 =
                       tts goal.FStar_Tactics_Types.context
                         goal.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1402 uu____1403 uu____1404
                      in
                   fail uu____1401)))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___97_1411 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___97_1411.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___97_1411.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___97_1411.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___97_1411.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___97_1411.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___97_1411.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___97_1411.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___97_1411.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___97_1411.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___97_1411.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1430 = FStar_Options.defensive ()  in
    if uu____1430
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
        let uu____1446 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1446 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1464 =
        (let uu____1467 = aux b2 env  in Prims.op_Negation uu____1467) &&
          (let uu____1469 = FStar_ST.op_Bang nwarn  in
           uu____1469 < (Prims.parse_int "5"))
         in
      (if uu____1464
       then
         ((let uu____1494 =
             let uu____1499 =
               let uu____1500 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1500
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1499)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1494);
          (let uu____1501 =
             let uu____1502 = FStar_ST.op_Bang nwarn  in
             uu____1502 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1501))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___98_1570 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_1570.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___98_1570.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___98_1570.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___98_1570.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_1570.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___98_1570.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___98_1570.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___98_1570.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___98_1570.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___98_1570.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___99_1590 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___99_1590.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___99_1590.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___99_1590.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___99_1590.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___99_1590.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___99_1590.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___99_1590.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___99_1590.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___99_1590.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___99_1590.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___100_1610 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_1610.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___100_1610.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___100_1610.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___100_1610.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___100_1610.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_1610.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_1610.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_1610.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_1610.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_1610.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___101_1630 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___101_1630.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___101_1630.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___101_1630.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___101_1630.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___101_1630.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___101_1630.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___101_1630.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___101_1630.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___101_1630.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___101_1630.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1641  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___102_1655 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___102_1655.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___102_1655.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___102_1655.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___102_1655.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___102_1655.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___102_1655.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___102_1655.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___102_1655.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___102_1655.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___102_1655.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1687 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1687 with
        | (u,uu____1703,g_u) ->
            let uu____1717 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1717 (fun uu____1721  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1727 = FStar_Syntax_Util.un_squash t  in
    match uu____1727 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1737 =
          let uu____1738 = FStar_Syntax_Subst.compress t'  in
          uu____1738.FStar_Syntax_Syntax.n  in
        (match uu____1737 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1742 -> false)
    | uu____1743 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1753 = FStar_Syntax_Util.un_squash t  in
    match uu____1753 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1763 =
          let uu____1764 = FStar_Syntax_Subst.compress t'  in
          uu____1764.FStar_Syntax_Syntax.n  in
        (match uu____1763 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1768 -> false)
    | uu____1769 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1780  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : unit -> unit tac) =
  fun uu____1797  ->
    let uu____1800 =
      let uu____1803 = cur_goal ()  in
      bind uu____1803
        (fun g  ->
           (let uu____1810 =
              let uu____1815 =
                let uu____1816 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1816
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1815)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1810);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1800
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1827  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___103_1837 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___103_1837.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___103_1837.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___103_1837.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___103_1837.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___103_1837.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___103_1837.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___103_1837.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___103_1837.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___103_1837.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___103_1837.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1838 = set ps1  in
         bind uu____1838
           (fun uu____1843  ->
              let uu____1844 = FStar_BigInt.of_int_fs n1  in ret uu____1844))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1851  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1859 = FStar_BigInt.of_int_fs n1  in ret uu____1859)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1872  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1880 = FStar_BigInt.of_int_fs n1  in ret uu____1880)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1893  ->
    let uu____1896 = cur_goal ()  in
    bind uu____1896 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1928 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1928 phi  in
          let uu____1929 = new_uvar reason env typ  in
          bind uu____1929
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
             (fun uu____1978  ->
                let uu____1979 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1979)
             (fun uu____1981  ->
                try
                  let uu____2001 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____2001
                with
                | FStar_Errors.Err (uu____2028,msg) ->
                    let uu____2030 = tts e t  in
                    let uu____2031 =
                      let uu____2032 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2032
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2030 uu____2031 msg
                | FStar_Errors.Error (uu____2039,msg,uu____2041) ->
                    let uu____2042 = tts e t  in
                    let uu____2043 =
                      let uu____2044 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2044
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____2042 uu____2043 msg))
  
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
  fun uu____2071  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___106_2089 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___106_2089.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___106_2089.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___106_2089.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___106_2089.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___106_2089.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___106_2089.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___106_2089.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___106_2089.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___106_2089.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___106_2089.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2113 = get_guard_policy ()  in
      bind uu____2113
        (fun old_pol  ->
           let uu____2119 = set_guard_policy pol  in
           bind uu____2119
             (fun uu____2123  ->
                bind t
                  (fun r  ->
                     let uu____2127 = set_guard_policy old_pol  in
                     bind uu____2127 (fun uu____2131  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2156 =
            let uu____2157 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2157.FStar_TypeChecker_Env.guard_f  in
          match uu____2156 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2161 = istrivial e f  in
              if uu____2161
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2169 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2169
                           (fun goal  ->
                              let goal1 =
                                let uu___107_2176 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___107_2176.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___107_2176.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___107_2176.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___107_2176.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2177 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2177
                           (fun goal  ->
                              let goal1 =
                                let uu___108_2184 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___108_2184.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___108_2184.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___108_2184.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___108_2184.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2192 =
                              let uu____2193 =
                                let uu____2194 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2194
                                 in
                              Prims.op_Negation uu____2193  in
                            if uu____2192
                            then
                              mlog
                                (fun uu____2199  ->
                                   let uu____2200 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2200)
                                (fun uu____2202  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2209 ->
                              mlog
                                (fun uu____2212  ->
                                   let uu____2213 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2213)
                                (fun uu____2215  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2225 =
      let uu____2228 = cur_goal ()  in
      bind uu____2228
        (fun goal  ->
           let uu____2234 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2234
             (fun uu____2254  ->
                match uu____2254 with
                | (t1,typ,guard) ->
                    let uu____2266 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2266 (fun uu____2270  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2225
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2299 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2299 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2310  ->
    let uu____2313 = cur_goal ()  in
    bind uu____2313
      (fun goal  ->
         let uu____2319 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2319
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2323 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2323))
  
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
          let uu____2352 =
            let uu____2353 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2353.FStar_TypeChecker_Env.guard_f  in
          match uu____2352 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2361 = istrivial e f  in
              if uu____2361
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2369 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2369
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___111_2379 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___111_2379.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___111_2379.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___111_2379.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___111_2379.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2386  ->
    let uu____2389 = cur_goal ()  in
    bind uu____2389
      (fun g  ->
         let uu____2395 = is_irrelevant g  in
         if uu____2395
         then bind __dismiss (fun uu____2399  -> add_smt_goals [g])
         else
           (let uu____2401 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2401))
  
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
             let uu____2450 =
               try
                 let uu____2484 =
                   let uu____2493 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2493 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2484
               with | uu____2515 -> fail "divide: not enough goals"  in
             bind uu____2450
               (fun uu____2542  ->
                  match uu____2542 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___112_2568 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___112_2568.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___112_2568.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___112_2568.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___112_2568.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___112_2568.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___112_2568.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___112_2568.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___112_2568.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___112_2568.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___113_2570 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___113_2570.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___113_2570.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___113_2570.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___113_2570.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___113_2570.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___113_2570.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___113_2570.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___113_2570.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___113_2570.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2571 = set lp  in
                      bind uu____2571
                        (fun uu____2579  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2593 = set rp  in
                                     bind uu____2593
                                       (fun uu____2601  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___114_2617 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___114_2617.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___114_2617.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2618 = set p'
                                                       in
                                                    bind uu____2618
                                                      (fun uu____2626  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2647 = divide FStar_BigInt.one f idtac  in
    bind uu____2647
      (fun uu____2660  -> match uu____2660 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2697::uu____2698 ->
             let uu____2701 =
               let uu____2710 = map tau  in
               divide FStar_BigInt.one tau uu____2710  in
             bind uu____2701
               (fun uu____2728  ->
                  match uu____2728 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2769 =
        bind t1
          (fun uu____2774  ->
             let uu____2775 = map t2  in
             bind uu____2775 (fun uu____2783  -> ret ()))
         in
      focus uu____2769
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2792  ->
    let uu____2795 =
      let uu____2798 = cur_goal ()  in
      bind uu____2798
        (fun goal  ->
           let uu____2807 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2807 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2822 =
                 let uu____2823 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2823  in
               if uu____2822
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2829 = new_uvar "intro" env' typ'  in
                  bind uu____2829
                    (fun u  ->
                       let uu____2835 =
                         let uu____2838 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2838  in
                       bind uu____2835
                         (fun bb  ->
                            if bb
                            then
                              let uu____2844 =
                                let uu____2847 =
                                  let uu___117_2848 = goal  in
                                  let uu____2849 = bnorm env' u  in
                                  let uu____2850 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2849;
                                    FStar_Tactics_Types.goal_ty = uu____2850;
                                    FStar_Tactics_Types.opts =
                                      (uu___117_2848.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___117_2848.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2847  in
                              bind uu____2844 (fun uu____2852  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2858 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2858)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2795
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2873  ->
    let uu____2880 = cur_goal ()  in
    bind uu____2880
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2897 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2897 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2916 =
                let uu____2917 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2917  in
              if uu____2916
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2933 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2933; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2935 =
                   let uu____2938 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2938  in
                 bind uu____2935
                   (fun u  ->
                      let lb =
                        let uu____2953 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2953 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2959 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2959 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2989 = trysolve goal tm  in
                          bind uu____2989
                            (fun bb  ->
                               if bb
                               then
                                 let uu____3005 =
                                   let uu____3008 =
                                     let uu___118_3009 = goal  in
                                     let uu____3010 = bnorm env' u  in
                                     let uu____3011 =
                                       let uu____3012 = comp_to_typ c  in
                                       bnorm env' uu____3012  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____3010;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____3011;
                                       FStar_Tactics_Types.opts =
                                         (uu___118_3009.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___118_3009.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____3008  in
                                 bind uu____3005
                                   (fun uu____3019  ->
                                      let uu____3020 =
                                        let uu____3025 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____3025, b)  in
                                      ret uu____3020)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____3039 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____3039))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3057 = cur_goal ()  in
    bind uu____3057
      (fun goal  ->
         mlog
           (fun uu____3064  ->
              let uu____3065 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3065)
           (fun uu____3070  ->
              let steps =
                let uu____3074 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3074
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
                (let uu___119_3081 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___119_3081.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___119_3081.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___119_3081.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3105 =
          mlog
            (fun uu____3110  ->
               let uu____3111 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3111)
            (fun uu____3113  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3119 -> g.FStar_Tactics_Types.opts
                      | uu____3122 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3127  ->
                         let uu____3128 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3128)
                      (fun uu____3131  ->
                         let uu____3132 = __tc e t  in
                         bind uu____3132
                           (fun uu____3153  ->
                              match uu____3153 with
                              | (t1,uu____3163,uu____3164) ->
                                  let steps =
                                    let uu____3168 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3168
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3105
  
let (refine_intro : unit -> unit tac) =
  fun uu____3182  ->
    let uu____3185 =
      let uu____3188 = cur_goal ()  in
      bind uu____3188
        (fun g  ->
           let uu____3195 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3195 with
           | (uu____3208,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___120_3233 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___120_3233.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___120_3233.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___120_3233.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___120_3233.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3234 =
                 let uu____3239 =
                   let uu____3244 =
                     let uu____3245 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3245]  in
                   FStar_Syntax_Subst.open_term uu____3244 phi  in
                 match uu____3239 with
                 | (bvs,phi1) ->
                     let uu____3252 =
                       let uu____3253 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3253  in
                     (uu____3252, phi1)
                  in
               (match uu____3234 with
                | (bv1,phi1) ->
                    let uu____3266 =
                      let uu____3269 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3269
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3266
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3273  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3185
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3292 = cur_goal ()  in
      bind uu____3292
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3301 = __tc env t  in
           bind uu____3301
             (fun uu____3320  ->
                match uu____3320 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3335  ->
                         let uu____3336 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3337 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3336 uu____3337)
                      (fun uu____3340  ->
                         let uu____3341 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3341
                           (fun uu____3345  ->
                              mlog
                                (fun uu____3349  ->
                                   let uu____3350 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3351 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3350 uu____3351)
                                (fun uu____3354  ->
                                   let uu____3355 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3355
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3363 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3364 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3365 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3366 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3363 uu____3364 uu____3365
                                             uu____3366)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3381 =
        mlog
          (fun uu____3386  ->
             let uu____3387 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3387)
          (fun uu____3390  ->
             let uu____3391 =
               let uu____3398 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3398  in
             bind uu____3391
               (fun uu___84_3407  ->
                  match uu___84_3407 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3417  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3420  ->
                           let uu____3421 =
                             let uu____3428 =
                               let uu____3431 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3431
                                 (fun uu____3436  ->
                                    let uu____3437 = refine_intro ()  in
                                    bind uu____3437
                                      (fun uu____3441  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3428  in
                           bind uu____3421
                             (fun uu___83_3448  ->
                                match uu___83_3448 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3456 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3381
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3475 =
             let uu____3482 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3482  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3475  in
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
          let uu____3552 = f x  in
          bind uu____3552
            (fun y  ->
               let uu____3560 = mapM f xs  in
               bind uu____3560 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3580 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3600 = cur_goal ()  in
        bind uu____3600
          (fun goal  ->
             mlog
               (fun uu____3607  ->
                  let uu____3608 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3608)
               (fun uu____3611  ->
                  let uu____3612 =
                    let uu____3617 =
                      let uu____3620 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3620  in
                    trytac_exn uu____3617  in
                  bind uu____3612
                    (fun uu___85_3627  ->
                       match uu___85_3627 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3635  ->
                                let uu____3636 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3636)
                             (fun uu____3639  ->
                                let uu____3640 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3640 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3672  ->
                                         let uu____3673 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3673)
                                      (fun uu____3676  ->
                                         let uu____3677 =
                                           let uu____3678 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3678  in
                                         if uu____3677
                                         then fail "not total codomain"
                                         else
                                           (let uu____3682 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3682
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3702 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3702
                                                    in
                                                 let uu____3703 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3703
                                                   (fun uu____3711  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3713 =
                                                        let uu____3714 =
                                                          let uu____3717 =
                                                            let uu____3718 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3718
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3717
                                                           in
                                                        uu____3714.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3713 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3746)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3774
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3774
                                                               then ret ()
                                                               else
                                                                 (let uu____3778
                                                                    =
                                                                    let uu____3781
                                                                    =
                                                                    let uu___121_3782
                                                                    = goal
                                                                     in
                                                                    let uu____3783
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3784
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___121_3782.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3783;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3784;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___121_3782.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3781]
                                                                     in
                                                                  add_goals
                                                                    uu____3778))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3839 =
        mlog
          (fun uu____3844  ->
             let uu____3845 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3845)
          (fun uu____3848  ->
             let uu____3849 = cur_goal ()  in
             bind uu____3849
               (fun goal  ->
                  let uu____3855 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3855
                    (fun uu____3877  ->
                       match uu____3877 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3890 =
                             let uu____3893 =
                               let uu____3896 = __apply uopt tm1 typ1  in
                               bind uu____3896
                                 (fun uu____3900  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3893  in
                           let uu____3901 =
                             let uu____3904 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3905 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3906 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3904 uu____3905 uu____3906
                              in
                           try_unif uu____3890 uu____3901)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3839
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3929 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3929
    then
      let uu____3936 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3955 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3996 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3936 with
      | (pre,post) ->
          let post1 =
            let uu____4032 =
              let uu____4041 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____4041]  in
            FStar_Syntax_Util.mk_app post uu____4032  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4055 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4055
       then
         let uu____4062 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4062
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4095 =
      let uu____4098 =
        mlog
          (fun uu____4103  ->
             let uu____4104 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4104)
          (fun uu____4108  ->
             let is_unit_t t =
               let uu____4115 =
                 let uu____4116 = FStar_Syntax_Subst.compress t  in
                 uu____4116.FStar_Syntax_Syntax.n  in
               match uu____4115 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4120 -> false  in
             let uu____4121 = cur_goal ()  in
             bind uu____4121
               (fun goal  ->
                  let uu____4127 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4127
                    (fun uu____4150  ->
                       match uu____4150 with
                       | (tm1,t,guard) ->
                           let uu____4162 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4162 with
                            | (bs,comp) ->
                                let uu____4189 = lemma_or_sq comp  in
                                (match uu____4189 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4208 =
                                       FStar_List.fold_left
                                         (fun uu____4250  ->
                                            fun uu____4251  ->
                                              match (uu____4250, uu____4251)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4342 =
                                                    is_unit_t b_t  in
                                                  if uu____4342
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4370 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4370 with
                                                     | (u,uu____4398,g_u) ->
                                                         let uu____4412 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4412,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4208 with
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
                                          let uu____4471 =
                                            let uu____4474 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4474
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4471
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4482 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4483 =
                                                   let uu____4484 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4484
                                                    in
                                                 let uu____4485 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4482 uu____4483
                                                   uu____4485
                                               else
                                                 (let uu____4487 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4487
                                                    (fun uu____4492  ->
                                                       let uu____4493 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4493
                                                         (fun uu____4501  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4516
                                                                  =
                                                                  let uu____4523
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4523
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4516
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
                                                              let uu____4572
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4572
                                                              with
                                                              | (hd1,uu____4588)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4610)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4635
                                                                    -> false)
                                                               in
                                                            let uu____4636 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4708
                                                                     ->
                                                                    match uu____4708
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4736)
                                                                    ->
                                                                    let uu____4737
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4737
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4763)
                                                                    ->
                                                                    let uu____4784
                                                                    =
                                                                    let uu____4785
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4785.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4784
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4798
                                                                    ->
                                                                    let uu____4815
                                                                    =
                                                                    let uu____4824
                                                                    =
                                                                    let uu____4827
                                                                    =
                                                                    let uu___124_4828
                                                                    = goal
                                                                     in
                                                                    let uu____4829
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4830
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___124_4828.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4829;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4830;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___124_4828.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___124_4828.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4827]
                                                                     in
                                                                    (uu____4824,
                                                                    [])  in
                                                                    ret
                                                                    uu____4815
                                                                    | 
                                                                    uu____4843
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4845
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4845
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4848
                                                                    =
                                                                    let uu____4855
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4855
                                                                    term1  in
                                                                    match uu____4848
                                                                    with
                                                                    | 
                                                                    (uu____4856,uu____4857,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4859
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4859
                                                                    (fun
                                                                    uu___86_4875
                                                                     ->
                                                                    match uu___86_4875
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
                                                            bind uu____4636
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4943
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4943
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4965
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4965
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____5026
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____5026
                                                                    then
                                                                    let uu____5029
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____5029
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
                                                                    let uu____5043
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5043)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5044
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5044
                                                                   (fun
                                                                    uu____5049
                                                                     ->
                                                                    let uu____5050
                                                                    =
                                                                    let uu____5053
                                                                    =
                                                                    let uu____5054
                                                                    =
                                                                    let uu____5055
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5055
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5054
                                                                     in
                                                                    if
                                                                    uu____5053
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
                                                                    uu____5050
                                                                    (fun
                                                                    uu____5061
                                                                     ->
                                                                    let uu____5062
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5062
                                                                    (fun
                                                                    uu____5066
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4098  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4095
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5088 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5088 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5098::(e1,uu____5100)::(e2,uu____5102)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5161 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5185 = destruct_eq' typ  in
    match uu____5185 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5215 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5215 with
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
        let uu____5277 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5277 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5325 = aux e'  in
               FStar_Util.map_opt uu____5325
                 (fun uu____5349  ->
                    match uu____5349 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5370 = aux e  in
      FStar_Util.map_opt uu____5370
        (fun uu____5394  ->
           match uu____5394 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5461 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5461
            (fun uu____5485  ->
               match uu____5485 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___125_5504 = bv  in
                     let uu____5505 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___125_5504.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___125_5504.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5505
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___126_5514 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___126_5514.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___126_5514.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5524 =
      let uu____5527 = cur_goal ()  in
      bind uu____5527
        (fun goal  ->
           let uu____5535 = h  in
           match uu____5535 with
           | (bv,uu____5539) ->
               mlog
                 (fun uu____5543  ->
                    let uu____5544 = FStar_Syntax_Print.bv_to_string bv  in
                    let uu____5545 =
                      tts goal.FStar_Tactics_Types.context
                        bv.FStar_Syntax_Syntax.sort
                       in
                    FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5544
                      uu____5545)
                 (fun uu____5548  ->
                    let uu____5549 =
                      split_env bv goal.FStar_Tactics_Types.context  in
                    match uu____5549 with
                    | FStar_Pervasives_Native.None  ->
                        fail "binder not found in environment"
                    | FStar_Pervasives_Native.Some (e0,bvs) ->
                        let uu____5578 =
                          destruct_eq bv.FStar_Syntax_Syntax.sort  in
                        (match uu____5578 with
                         | FStar_Pervasives_Native.Some (x,e) ->
                             let uu____5593 =
                               let uu____5594 = FStar_Syntax_Subst.compress x
                                  in
                               uu____5594.FStar_Syntax_Syntax.n  in
                             (match uu____5593 with
                              | FStar_Syntax_Syntax.Tm_name x1 ->
                                  let s = [FStar_Syntax_Syntax.NT (x1, e)]
                                     in
                                  let s1 bv1 =
                                    let uu___127_5609 = bv1  in
                                    let uu____5610 =
                                      FStar_Syntax_Subst.subst s
                                        bv1.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___127_5609.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___127_5609.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____5610
                                    }  in
                                  let bvs1 = FStar_List.map s1 bvs  in
                                  let uu____5616 =
                                    let uu___128_5617 = goal  in
                                    let uu____5618 = push_bvs e0 (bv :: bvs1)
                                       in
                                    let uu____5619 =
                                      FStar_Syntax_Subst.subst s
                                        goal.FStar_Tactics_Types.witness
                                       in
                                    let uu____5620 =
                                      FStar_Syntax_Subst.subst s
                                        goal.FStar_Tactics_Types.goal_ty
                                       in
                                    {
                                      FStar_Tactics_Types.context =
                                        uu____5618;
                                      FStar_Tactics_Types.witness =
                                        uu____5619;
                                      FStar_Tactics_Types.goal_ty =
                                        uu____5620;
                                      FStar_Tactics_Types.opts =
                                        (uu___128_5617.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___128_5617.FStar_Tactics_Types.is_guard)
                                    }  in
                                  replace_cur uu____5616
                              | uu____5621 ->
                                  fail
                                    "Not an equality hypothesis with a variable on the LHS")
                         | uu____5622 -> fail "Not an equality hypothesis")))
       in
    FStar_All.pipe_left (wrap_err "rewrite") uu____5524
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5647 =
        let uu____5650 = cur_goal ()  in
        bind uu____5650
          (fun goal  ->
             let uu____5661 = b  in
             match uu____5661 with
             | (bv,uu____5665) ->
                 let bv' =
                   let uu____5667 =
                     let uu___129_5668 = bv  in
                     let uu____5669 =
                       FStar_Ident.mk_ident
                         (s,
                           ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                        in
                     {
                       FStar_Syntax_Syntax.ppname = uu____5669;
                       FStar_Syntax_Syntax.index =
                         (uu___129_5668.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort =
                         (uu___129_5668.FStar_Syntax_Syntax.sort)
                     }  in
                   FStar_Syntax_Syntax.freshen_bv uu____5667  in
                 let s1 =
                   let uu____5673 =
                     let uu____5674 =
                       let uu____5681 = FStar_Syntax_Syntax.bv_to_name bv'
                          in
                       (bv, uu____5681)  in
                     FStar_Syntax_Syntax.NT uu____5674  in
                   [uu____5673]  in
                 let uu____5682 = subst_goal bv bv' s1 goal  in
                 (match uu____5682 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder not found in environment"
                  | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
         in
      FStar_All.pipe_left (wrap_err "rename_to") uu____5647
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5701 =
      let uu____5704 = cur_goal ()  in
      bind uu____5704
        (fun goal  ->
           let uu____5713 = b  in
           match uu____5713 with
           | (bv,uu____5717) ->
               let uu____5718 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5718 with
                | FStar_Pervasives_Native.None  ->
                    fail "binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let uu____5747 = FStar_Syntax_Util.type_u ()  in
                    (match uu____5747 with
                     | (ty,u) ->
                         let uu____5756 = new_uvar "binder_retype" e0 ty  in
                         bind uu____5756
                           (fun t'  ->
                              let bv'' =
                                let uu___130_5766 = bv  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___130_5766.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___130_5766.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t'
                                }  in
                              let s =
                                let uu____5770 =
                                  let uu____5771 =
                                    let uu____5778 =
                                      FStar_Syntax_Syntax.bv_to_name bv''  in
                                    (bv, uu____5778)  in
                                  FStar_Syntax_Syntax.NT uu____5771  in
                                [uu____5770]  in
                              let bvs1 =
                                FStar_List.map
                                  (fun b1  ->
                                     let uu___131_5786 = b1  in
                                     let uu____5787 =
                                       FStar_Syntax_Subst.subst s
                                         b1.FStar_Syntax_Syntax.sort
                                        in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         (uu___131_5786.FStar_Syntax_Syntax.ppname);
                                       FStar_Syntax_Syntax.index =
                                         (uu___131_5786.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort = uu____5787
                                     }) bvs
                                 in
                              let env' = push_bvs e0 (bv'' :: bvs1)  in
                              bind __dismiss
                                (fun uu____5793  ->
                                   let uu____5794 =
                                     let uu____5797 =
                                       let uu____5800 =
                                         let uu___132_5801 = goal  in
                                         let uu____5802 =
                                           FStar_Syntax_Subst.subst s
                                             goal.FStar_Tactics_Types.witness
                                            in
                                         let uu____5803 =
                                           FStar_Syntax_Subst.subst s
                                             goal.FStar_Tactics_Types.goal_ty
                                            in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness =
                                             uu____5802;
                                           FStar_Tactics_Types.goal_ty =
                                             uu____5803;
                                           FStar_Tactics_Types.opts =
                                             (uu___132_5801.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___132_5801.FStar_Tactics_Types.is_guard)
                                         }  in
                                       [uu____5800]  in
                                     add_goals uu____5797  in
                                   bind uu____5794
                                     (fun uu____5806  ->
                                        let uu____5807 =
                                          FStar_Syntax_Util.mk_eq2
                                            (FStar_Syntax_Syntax.U_succ u) ty
                                            bv.FStar_Syntax_Syntax.sort t'
                                           in
                                        add_irrelevant_goal
                                          "binder_retype equation" e0
                                          uu____5807
                                          goal.FStar_Tactics_Types.opts))))))
       in
    FStar_All.pipe_left (wrap_err "binder_retype") uu____5701
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5830 =
        let uu____5833 = cur_goal ()  in
        bind uu____5833
          (fun goal  ->
             let uu____5842 = b  in
             match uu____5842 with
             | (bv,uu____5846) ->
                 let uu____5847 =
                   split_env bv goal.FStar_Tactics_Types.context  in
                 (match uu____5847 with
                  | FStar_Pervasives_Native.None  ->
                      fail "binder is not present in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let steps =
                        let uu____5879 =
                          FStar_TypeChecker_Normalize.tr_norm_steps s  in
                        FStar_List.append
                          [FStar_TypeChecker_Normalize.Reify;
                          FStar_TypeChecker_Normalize.UnfoldTac] uu____5879
                         in
                      let sort' =
                        normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                      let bv' =
                        let uu___133_5884 = bv  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___133_5884.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___133_5884.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = sort'
                        }  in
                      let env' = push_bvs e0 (bv' :: bvs)  in
                      replace_cur
                        (let uu___134_5888 = goal  in
                         {
                           FStar_Tactics_Types.context = env';
                           FStar_Tactics_Types.witness =
                             (uu___134_5888.FStar_Tactics_Types.witness);
                           FStar_Tactics_Types.goal_ty =
                             (uu___134_5888.FStar_Tactics_Types.goal_ty);
                           FStar_Tactics_Types.opts =
                             (uu___134_5888.FStar_Tactics_Types.opts);
                           FStar_Tactics_Types.is_guard =
                             (uu___134_5888.FStar_Tactics_Types.is_guard)
                         })))
         in
      FStar_All.pipe_left (wrap_err "norm_binder_type") uu____5830
  
let (revert : unit -> unit tac) =
  fun uu____5899  ->
    let uu____5902 = cur_goal ()  in
    bind uu____5902
      (fun goal  ->
         let uu____5908 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5908 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5930 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5930
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___135_5964 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___135_5964.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___135_5964.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5975 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5975
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5988 = cur_goal ()  in
    bind uu____5988
      (fun goal  ->
         mlog
           (fun uu____5996  ->
              let uu____5997 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5998 =
                let uu____5999 =
                  let uu____6000 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____6000 FStar_List.length  in
                FStar_All.pipe_right uu____5999 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5997 uu____5998)
           (fun uu____6011  ->
              let uu____6012 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____6012 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____6059 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____6059
                        then
                          let uu____6062 =
                            let uu____6063 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____6063
                             in
                          fail uu____6062
                        else check1 bvs2
                     in
                  let uu____6065 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____6065
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____6069 = check1 bvs  in
                     bind uu____6069
                       (fun uu____6075  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6077 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6077
                            (fun ut  ->
                               let uu____6083 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6083
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___136_6092 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___136_6092.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___136_6092.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___136_6092.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6100  ->
    let uu____6103 = cur_goal ()  in
    bind uu____6103
      (fun goal  ->
         let uu____6109 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6109 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6123) ->
             let uu____6128 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6128)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6138 = cur_goal ()  in
    bind uu____6138
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6148 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6148  in
         let g' =
           let uu___137_6150 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___137_6150.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___137_6150.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___137_6150.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___137_6150.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6152  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6162 = cur_goal ()  in
    bind uu____6162
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6172 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6172  in
         let g' =
           let uu___138_6174 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___138_6174.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___138_6174.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___138_6174.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___138_6174.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6176  -> add_goals [g']))
  
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
            let uu____6216 = FStar_Syntax_Subst.compress t  in
            uu____6216.FStar_Syntax_Syntax.n  in
          let uu____6219 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___142_6225 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___142_6225.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___142_6225.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6219
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6241 =
                   let uu____6242 = FStar_Syntax_Subst.compress t1  in
                   uu____6242.FStar_Syntax_Syntax.n  in
                 match uu____6241 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6269 = ff hd1  in
                     bind uu____6269
                       (fun hd2  ->
                          let fa uu____6291 =
                            match uu____6291 with
                            | (a,q) ->
                                let uu____6304 = ff a  in
                                bind uu____6304 (fun a1  -> ret (a1, q))
                             in
                          let uu____6317 = mapM fa args  in
                          bind uu____6317
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6377 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6377 with
                      | (bs1,t') ->
                          let uu____6386 =
                            let uu____6389 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6389 t'  in
                          bind uu____6386
                            (fun t''  ->
                               let uu____6393 =
                                 let uu____6394 =
                                   let uu____6411 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6412 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6411, uu____6412, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6394  in
                               ret uu____6393))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6471 = ff hd1  in
                     bind uu____6471
                       (fun hd2  ->
                          let ffb br =
                            let uu____6486 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6486 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6518 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6518  in
                                let uu____6519 = ff1 e  in
                                bind uu____6519
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6532 = mapM ffb brs  in
                          bind uu____6532
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6546;
                          FStar_Syntax_Syntax.lbtyp = uu____6547;
                          FStar_Syntax_Syntax.lbeff = uu____6548;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6550;
                          FStar_Syntax_Syntax.lbpos = uu____6551;_}::[]),e)
                     ->
                     let lb =
                       let uu____6576 =
                         let uu____6577 = FStar_Syntax_Subst.compress t1  in
                         uu____6577.FStar_Syntax_Syntax.n  in
                       match uu____6576 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6581) -> lb
                       | uu____6594 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6603 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6603
                         (fun def1  ->
                            ret
                              (let uu___139_6609 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___139_6609.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___139_6609.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___139_6609.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___139_6609.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___139_6609.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___139_6609.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6610 = fflb lb  in
                     bind uu____6610
                       (fun lb1  ->
                          let uu____6620 =
                            let uu____6625 =
                              let uu____6626 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6626]  in
                            FStar_Syntax_Subst.open_term uu____6625 e  in
                          match uu____6620 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6638 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6638  in
                              let uu____6639 = ff1 e1  in
                              bind uu____6639
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6678 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6678
                         (fun def  ->
                            ret
                              (let uu___140_6684 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___140_6684.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___140_6684.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___140_6684.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___140_6684.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___140_6684.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___140_6684.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6685 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6685 with
                      | (lbs1,e1) ->
                          let uu____6700 = mapM fflb lbs1  in
                          bind uu____6700
                            (fun lbs2  ->
                               let uu____6712 = ff e1  in
                               bind uu____6712
                                 (fun e2  ->
                                    let uu____6720 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6720 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6786 = ff t2  in
                     bind uu____6786
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6815 = ff t2  in
                     bind uu____6815
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6820 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___141_6827 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___141_6827.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___141_6827.FStar_Syntax_Syntax.vars)
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
            let uu____6866 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6866 with
            | (t1,lcomp,g) ->
                let uu____6878 =
                  (let uu____6881 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6881) ||
                    (let uu____6883 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6883)
                   in
                if uu____6878
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6891 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6891
                       (fun ut  ->
                          log ps
                            (fun uu____6902  ->
                               let uu____6903 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6904 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6903 uu____6904);
                          (let uu____6905 =
                             let uu____6908 =
                               let uu____6909 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6909 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6908 opts
                              in
                           bind uu____6905
                             (fun uu____6912  ->
                                let uu____6913 =
                                  bind tau
                                    (fun uu____6919  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6925  ->
                                            let uu____6926 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6927 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6926 uu____6927);
                                       ret ut1)
                                   in
                                focus uu____6913)))
                      in
                   let uu____6928 = trytac' rewrite_eq  in
                   bind uu____6928
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
          let uu____7100 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7100
            (fun t1  ->
               let uu____7104 =
                 f env
                   (let uu___145_7113 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___145_7113.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___145_7113.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7104
                 (fun uu____7125  ->
                    match uu____7125 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7144 =
                               let uu____7145 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7145.FStar_Syntax_Syntax.n  in
                             match uu____7144 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7178 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7178
                                   (fun uu____7203  ->
                                      match uu____7203 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7219 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7219
                                            (fun uu____7246  ->
                                               match uu____7246 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___143_7276 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___143_7276.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___143_7276.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7302 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7302 with
                                  | (bs1,t') ->
                                      let uu____7317 =
                                        let uu____7324 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7324 ctrl1 t'
                                         in
                                      bind uu____7317
                                        (fun uu____7342  ->
                                           match uu____7342 with
                                           | (t'',ctrl2) ->
                                               let uu____7357 =
                                                 let uu____7364 =
                                                   let uu___144_7367 = t4  in
                                                   let uu____7370 =
                                                     let uu____7371 =
                                                       let uu____7388 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7389 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7388,
                                                         uu____7389, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7371
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7370;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___144_7367.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___144_7367.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7364, ctrl2)  in
                                               ret uu____7357))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7422 -> ret (t3, ctrl1))))

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
              let uu____7473 = ctrl_tac_fold f env ctrl t  in
              bind uu____7473
                (fun uu____7501  ->
                   match uu____7501 with
                   | (t1,ctrl1) ->
                       let uu____7520 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7520
                         (fun uu____7551  ->
                            match uu____7551 with
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
              let uu____7647 =
                let uu____7654 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7654
                  (fun uu____7663  ->
                     let uu____7664 = ctrl t1  in
                     bind uu____7664
                       (fun res  ->
                          let uu____7687 = trivial ()  in
                          bind uu____7687 (fun uu____7695  -> ret res)))
                 in
              bind uu____7647
                (fun uu____7711  ->
                   match uu____7711 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7735 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7735 with
                          | (t2,lcomp,g) ->
                              let uu____7751 =
                                (let uu____7754 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7754) ||
                                  (let uu____7756 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7756)
                                 in
                              if uu____7751
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7769 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7769
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7784  ->
                                           let uu____7785 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7786 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7785 uu____7786);
                                      (let uu____7787 =
                                         let uu____7790 =
                                           let uu____7791 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7791 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7790 opts
                                          in
                                       bind uu____7787
                                         (fun uu____7798  ->
                                            let uu____7799 =
                                              bind rewriter
                                                (fun uu____7813  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7819  ->
                                                        let uu____7820 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7821 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7820
                                                          uu____7821);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7799))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      let uu____7862 =
        bind get
          (fun ps  ->
             let uu____7872 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____7872 with
             | (g,gs) ->
                 let gt1 = g.FStar_Tactics_Types.goal_ty  in
                 (log ps
                    (fun uu____7909  ->
                       let uu____7910 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                         uu____7910);
                  bind dismiss_all
                    (fun uu____7913  ->
                       let uu____7914 =
                         ctrl_tac_fold
                           (rewrite_rec ps ctrl rewriter
                              g.FStar_Tactics_Types.opts)
                           g.FStar_Tactics_Types.context keepGoing gt1
                          in
                       bind uu____7914
                         (fun uu____7932  ->
                            match uu____7932 with
                            | (gt',uu____7940) ->
                                (log ps
                                   (fun uu____7944  ->
                                      let uu____7945 =
                                        FStar_Syntax_Print.term_to_string gt'
                                         in
                                      FStar_Util.print1
                                        "Topdown_rewrite seems to have succeded with %s\n"
                                        uu____7945);
                                 (let uu____7946 = push_goals gs  in
                                  bind uu____7946
                                    (fun uu____7950  ->
                                       add_goals
                                         [(let uu___146_7952 = g  in
                                           {
                                             FStar_Tactics_Types.context =
                                               (uu___146_7952.FStar_Tactics_Types.context);
                                             FStar_Tactics_Types.witness =
                                               (uu___146_7952.FStar_Tactics_Types.witness);
                                             FStar_Tactics_Types.goal_ty =
                                               gt';
                                             FStar_Tactics_Types.opts =
                                               (uu___146_7952.FStar_Tactics_Types.opts);
                                             FStar_Tactics_Types.is_guard =
                                               (uu___146_7952.FStar_Tactics_Types.is_guard)
                                           })])))))))
         in
      FStar_All.pipe_left (wrap_err "topdown_rewrite") uu____7862
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      let uu____7975 =
        bind get
          (fun ps  ->
             let uu____7985 =
               match ps.FStar_Tactics_Types.goals with
               | g::gs -> (g, gs)
               | [] -> failwith "no goals"  in
             match uu____7985 with
             | (g,gs) ->
                 let gt1 = g.FStar_Tactics_Types.goal_ty  in
                 (log ps
                    (fun uu____8022  ->
                       let uu____8023 = FStar_Syntax_Print.term_to_string gt1
                          in
                       FStar_Util.print1 "Pointwise starting with %s\n"
                         uu____8023);
                  bind dismiss_all
                    (fun uu____8026  ->
                       let uu____8027 =
                         tac_fold_env d
                           (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                           g.FStar_Tactics_Types.context gt1
                          in
                       bind uu____8027
                         (fun gt'  ->
                            log ps
                              (fun uu____8037  ->
                                 let uu____8038 =
                                   FStar_Syntax_Print.term_to_string gt'  in
                                 FStar_Util.print1
                                   "Pointwise seems to have succeded with %s\n"
                                   uu____8038);
                            (let uu____8039 = push_goals gs  in
                             bind uu____8039
                               (fun uu____8043  ->
                                  add_goals
                                    [(let uu___147_8045 = g  in
                                      {
                                        FStar_Tactics_Types.context =
                                          (uu___147_8045.FStar_Tactics_Types.context);
                                        FStar_Tactics_Types.witness =
                                          (uu___147_8045.FStar_Tactics_Types.witness);
                                        FStar_Tactics_Types.goal_ty = gt';
                                        FStar_Tactics_Types.opts =
                                          (uu___147_8045.FStar_Tactics_Types.opts);
                                        FStar_Tactics_Types.is_guard =
                                          (uu___147_8045.FStar_Tactics_Types.is_guard)
                                      })]))))))
         in
      FStar_All.pipe_left (wrap_err "pointwise") uu____7975
  
let (trefl : unit -> unit tac) =
  fun uu____8056  ->
    let uu____8059 =
      let uu____8062 = cur_goal ()  in
      bind uu____8062
        (fun g  ->
           let uu____8080 =
             FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
           match uu____8080 with
           | FStar_Pervasives_Native.Some t ->
               let uu____8092 = FStar_Syntax_Util.head_and_args' t  in
               (match uu____8092 with
                | (hd1,args) ->
                    let uu____8125 =
                      let uu____8138 =
                        let uu____8139 = FStar_Syntax_Util.un_uinst hd1  in
                        uu____8139.FStar_Syntax_Syntax.n  in
                      (uu____8138, args)  in
                    (match uu____8125 with
                     | (FStar_Syntax_Syntax.Tm_fvar
                        fv,uu____8153::(l,uu____8155)::(r,uu____8157)::[])
                         when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu____8204 =
                           do_unify g.FStar_Tactics_Types.context l r  in
                         bind uu____8204
                           (fun b  ->
                              if Prims.op_Negation b
                              then
                                let uu____8213 =
                                  tts g.FStar_Tactics_Types.context l  in
                                let uu____8214 =
                                  tts g.FStar_Tactics_Types.context r  in
                                fail2 "not a trivial equality (%s vs %s)"
                                  uu____8213 uu____8214
                              else solve g FStar_Syntax_Util.exp_unit)
                     | (hd2,uu____8217) ->
                         let uu____8234 = tts g.FStar_Tactics_Types.context t
                            in
                         fail1 "not an equality (%s)" uu____8234))
           | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
       in
    FStar_All.pipe_left (wrap_err "trefl") uu____8059
  
let (dup : unit -> unit tac) =
  fun uu____8247  ->
    let uu____8250 = cur_goal ()  in
    bind uu____8250
      (fun g  ->
         let uu____8256 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8256
           (fun u  ->
              let g' =
                let uu___148_8263 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___148_8263.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___148_8263.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___148_8263.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___148_8263.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8266  ->
                   let uu____8267 =
                     let uu____8270 =
                       let uu____8271 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8271
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8270
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8267
                     (fun uu____8274  ->
                        let uu____8275 = add_goals [g']  in
                        bind uu____8275 (fun uu____8279  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8286  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___149_8303 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___149_8303.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___149_8303.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___149_8303.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___149_8303.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___149_8303.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___149_8303.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___149_8303.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___149_8303.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___149_8303.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___149_8303.FStar_Tactics_Types.freshness)
                })
         | uu____8304 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8313  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___150_8326 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___150_8326.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___150_8326.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___150_8326.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___150_8326.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___150_8326.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___150_8326.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___150_8326.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___150_8326.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___150_8326.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___150_8326.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8333  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8340 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8360 =
      let uu____8367 = cur_goal ()  in
      bind uu____8367
        (fun g  ->
           let uu____8377 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8377
             (fun uu____8413  ->
                match uu____8413 with
                | (t1,typ,guard) ->
                    let uu____8429 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8429 with
                     | (hd1,args) ->
                         let uu____8472 =
                           let uu____8485 =
                             let uu____8486 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8486.FStar_Syntax_Syntax.n  in
                           (uu____8485, args)  in
                         (match uu____8472 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8505)::(q,uu____8507)::[]) when
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
                                let uu___151_8545 = g  in
                                let uu____8546 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8546;
                                  FStar_Tactics_Types.witness =
                                    (uu___151_8545.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___151_8545.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___151_8545.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___151_8545.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___152_8548 = g  in
                                let uu____8549 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8549;
                                  FStar_Tactics_Types.witness =
                                    (uu___152_8548.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___152_8548.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___152_8548.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___152_8548.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8556  ->
                                   let uu____8557 = add_goals [g1; g2]  in
                                   bind uu____8557
                                     (fun uu____8566  ->
                                        let uu____8567 =
                                          let uu____8572 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8573 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8572, uu____8573)  in
                                        ret uu____8567))
                          | uu____8578 ->
                              let uu____8591 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8591))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8360
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8621 =
      let uu____8624 = cur_goal ()  in
      bind uu____8624
        (fun g  ->
           FStar_Options.push ();
           (let uu____8637 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
               in
            FStar_Options.set uu____8637);
           (let res = FStar_Options.set_options FStar_Options.Set s  in
            let opts' = FStar_Options.peek ()  in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success  ->
                 let g' =
                   let uu___153_8644 = g  in
                   {
                     FStar_Tactics_Types.context =
                       (uu___153_8644.FStar_Tactics_Types.context);
                     FStar_Tactics_Types.witness =
                       (uu___153_8644.FStar_Tactics_Types.witness);
                     FStar_Tactics_Types.goal_ty =
                       (uu___153_8644.FStar_Tactics_Types.goal_ty);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (uu___153_8644.FStar_Tactics_Types.is_guard)
                   }  in
                 replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help  ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s)))
       in
    FStar_All.pipe_left (wrap_err "set_options") uu____8621
  
let (top_env : unit -> env tac) =
  fun uu____8656  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8669  ->
    let uu____8672 = cur_goal ()  in
    bind uu____8672
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8685  ->
    let uu____8688 = cur_goal ()  in
    bind uu____8688
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8701  ->
    let uu____8704 = cur_goal ()  in
    bind uu____8704
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8725 =
        let uu____8728 = cur_goal ()  in
        bind uu____8728
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8736 = __tc env tm  in
             bind uu____8736
               (fun uu____8756  ->
                  match uu____8756 with
                  | (tm1,typ,guard) ->
                      let uu____8768 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8768 (fun uu____8772  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8725
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8795 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8801 =
              let uu____8802 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8802  in
            new_uvar "uvar_env.2" env uu____8801
         in
      bind uu____8795
        (fun typ  ->
           let uu____8814 = new_uvar "uvar_env" env typ  in
           bind uu____8814 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8828 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8845 -> g.FStar_Tactics_Types.opts
             | uu____8848 -> FStar_Options.peek ()  in
           let uu____8851 = FStar_Syntax_Util.head_and_args t  in
           match uu____8851 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8868,typ);
                FStar_Syntax_Syntax.pos = uu____8870;
                FStar_Syntax_Syntax.vars = uu____8871;_},uu____8872)
               ->
               let uu____8917 =
                 let uu____8920 =
                   let uu____8921 = bnorm env t  in
                   let uu____8922 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8921;
                     FStar_Tactics_Types.goal_ty = uu____8922;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8920]  in
               add_goals uu____8917
           | uu____8923 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8828
  
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
          (fun uu____8984  ->
             let uu____8985 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8985
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
        (fun uu____9006  ->
           let uu____9007 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____9007)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____9017 =
      mlog
        (fun uu____9022  ->
           let uu____9023 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____9023)
        (fun uu____9026  ->
           let uu____9027 = cur_goal ()  in
           bind uu____9027
             (fun g  ->
                let uu____9033 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____9033
                  (fun uu____9053  ->
                     match uu____9053 with
                     | (ty1,uu____9063,guard) ->
                         let uu____9065 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____9065
                           (fun uu____9070  ->
                              let uu____9071 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____9071
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___154_9080 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___154_9080.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___154_9080.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___154_9080.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___154_9080.FStar_Tactics_Types.is_guard)
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
                                      let uu____9087 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____9087
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___155_9096 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___155_9096.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___155_9096.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___155_9096.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___155_9096.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____9017
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9118::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9146 = init xs  in x :: uu____9146
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let uu____9158 =
      let t1 = FStar_Syntax_Util.unascribe t  in
      let t2 = FStar_Syntax_Util.un_uinst t1  in
      match t2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t3,uu____9166) -> inspect t3
      | FStar_Syntax_Syntax.Tm_name bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
      | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
          failwith "empty arguments on Tm_app"
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let uu____9223 = last args  in
          (match uu____9223 with
           | (a,q) ->
               let q' = FStar_Reflection_Basic.inspect_aqual q  in
               let uu____9245 =
                 let uu____9246 =
                   let uu____9251 =
                     let uu____9254 =
                       let uu____9259 = init args  in
                       FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9259  in
                     uu____9254 FStar_Pervasives_Native.None
                       t2.FStar_Syntax_Syntax.pos
                      in
                   (uu____9251, (a, q'))  in
                 FStar_Reflection_Data.Tv_App uu____9246  in
               FStar_All.pipe_left ret uu____9245)
      | FStar_Syntax_Syntax.Tm_abs ([],uu____9280,uu____9281) ->
          failwith "empty arguments on Tm_abs"
      | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
          let uu____9325 = FStar_Syntax_Subst.open_term bs t3  in
          (match uu____9325 with
           | (bs1,t4) ->
               (match bs1 with
                | [] -> failwith "impossible"
                | b::bs2 ->
                    let uu____9358 =
                      let uu____9359 =
                        let uu____9364 = FStar_Syntax_Util.abs bs2 t4 k  in
                        (b, uu____9364)  in
                      FStar_Reflection_Data.Tv_Abs uu____9359  in
                    FStar_All.pipe_left ret uu____9358))
      | FStar_Syntax_Syntax.Tm_type uu____9371 ->
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
      | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
          failwith "empty binders on arrow"
      | FStar_Syntax_Syntax.Tm_arrow uu____9391 ->
          let uu____9404 = FStar_Syntax_Util.arrow_one t2  in
          (match uu____9404 with
           | FStar_Pervasives_Native.Some (b,c) ->
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Arrow (b, c))
           | FStar_Pervasives_Native.None  -> failwith "impossible")
      | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
          let b = FStar_Syntax_Syntax.mk_binder bv  in
          let uu____9434 = FStar_Syntax_Subst.open_term [b] t3  in
          (match uu____9434 with
           | (b',t4) ->
               let b1 =
                 match b' with
                 | b'1::[] -> b'1
                 | uu____9465 -> failwith "impossible"  in
               FStar_All.pipe_left ret
                 (FStar_Reflection_Data.Tv_Refine
                    ((FStar_Pervasives_Native.fst b1), t4)))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____9473 =
            let uu____9474 = FStar_Reflection_Basic.inspect_const c  in
            FStar_Reflection_Data.Tv_Const uu____9474  in
          FStar_All.pipe_left ret uu____9473
      | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
          let uu____9503 =
            let uu____9504 =
              let uu____9509 =
                let uu____9510 = FStar_Syntax_Unionfind.uvar_id u  in
                FStar_BigInt.of_int_fs uu____9510  in
              (uu____9509, t3)  in
            FStar_Reflection_Data.Tv_Uvar uu____9504  in
          FStar_All.pipe_left ret uu____9503
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
          if lb.FStar_Syntax_Syntax.lbunivs <> []
          then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
          else
            (match lb.FStar_Syntax_Syntax.lbname with
             | FStar_Util.Inr uu____9538 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let b = FStar_Syntax_Syntax.mk_binder bv  in
                 let uu____9543 = FStar_Syntax_Subst.open_term [b] t21  in
                 (match uu____9543 with
                  | (bs,t22) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____9574 ->
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
             | FStar_Util.Inr uu____9606 ->
                 FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
             | FStar_Util.Inl bv ->
                 let uu____9610 = FStar_Syntax_Subst.open_let_rec [lb] t21
                    in
                 (match uu____9610 with
                  | (lbs,t22) ->
                      (match lbs with
                       | lb1::[] ->
                           (match lb1.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____9630 ->
                                ret FStar_Reflection_Data.Tv_Unknown
                            | FStar_Util.Inl bv1 ->
                                FStar_All.pipe_left ret
                                  (FStar_Reflection_Data.Tv_Let
                                     (true, bv1,
                                       (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                       | uu____9636 ->
                           failwith
                             "impossible: open_term returned different amount of binders")))
      | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
          let rec inspect_pat p =
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let uu____9690 = FStar_Reflection_Basic.inspect_const c  in
                FStar_Reflection_Data.Pat_Constant uu____9690
            | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
                let uu____9709 =
                  let uu____9716 =
                    FStar_List.map
                      (fun uu____9728  ->
                         match uu____9728 with
                         | (p1,uu____9736) -> inspect_pat p1) ps
                     in
                  (fv, uu____9716)  in
                FStar_Reflection_Data.Pat_Cons uu____9709
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
              (fun uu___87_9790  ->
                 match uu___87_9790 with
                 | (pat,uu____9812,t4) ->
                     let uu____9830 = inspect_pat pat  in (uu____9830, t4))
              brs1
             in
          FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
      | FStar_Syntax_Syntax.Tm_unknown  ->
          FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
      | uu____9847 ->
          ((let uu____9849 =
              let uu____9854 =
                let uu____9855 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____9856 = FStar_Syntax_Print.term_to_string t2  in
                FStar_Util.format2
                  "inspect: outside of expected syntax (%s, %s)\n" uu____9855
                  uu____9856
                 in
              (FStar_Errors.Warning_CantInspect, uu____9854)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9849);
           FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
       in
    wrap_err "inspect" uu____9158
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9869 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9869
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9873 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9873
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9877 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9877
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9888 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9888
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9909 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9909
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9914 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9914
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9929 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9929
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9941 =
          let uu____9944 =
            let uu____9951 =
              let uu____9952 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9952  in
            FStar_Syntax_Syntax.mk uu____9951  in
          uu____9944 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9941
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9966 =
          let uu____9969 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9969 t  in
        FStar_All.pipe_left ret uu____9966
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9984 =
          let uu____9987 =
            let uu____9994 =
              let uu____9995 =
                let uu____10008 =
                  let uu____10009 =
                    let uu____10010 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____10010]  in
                  FStar_Syntax_Subst.close uu____10009 t2  in
                ((false, [lb]), uu____10008)  in
              FStar_Syntax_Syntax.Tm_let uu____9995  in
            FStar_Syntax_Syntax.mk uu____9994  in
          uu____9987 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9984
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____10036 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____10036 with
         | (lbs,body) ->
             let uu____10051 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____10051)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____10091 =
                let uu____10092 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____10092  in
              FStar_All.pipe_left wrap uu____10091
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____10101 =
                let uu____10102 =
                  let uu____10115 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10129 = pack_pat p1  in
                         (uu____10129, false)) ps
                     in
                  (fv, uu____10115)  in
                FStar_Syntax_Syntax.Pat_cons uu____10102  in
              FStar_All.pipe_left wrap uu____10101
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
            (fun uu___88_10179  ->
               match uu___88_10179 with
               | (pat,t1) ->
                   let uu____10196 = pack_pat pat  in
                   (uu____10196, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10206 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10206
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10226 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10226
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10268 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10268
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10303 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10303
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10332 =
        FStar_TypeChecker_Util.new_implicit_var "goal_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10332 with
      | (u,uu____10350,g_u) ->
          let g =
            let uu____10365 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10365;
              FStar_Tactics_Types.is_guard = false
            }  in
          (g, g_u)
  
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
        let uu____10385 = goal_of_goal_ty env typ  in
        match uu____10385 with
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
            (ps, (g.FStar_Tactics_Types.witness))
  