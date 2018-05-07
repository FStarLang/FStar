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
let ret : 'a . 'a -> 'a tac =
  fun x  -> mk_tac (fun p  -> FStar_Tactics_Result.Success (x, p)) 
let bind : 'a 'b . 'a tac -> ('a -> 'b tac) -> 'b tac =
  fun t1  ->
    fun t2  ->
      mk_tac
        (fun p  ->
           let uu____179 = run t1 p  in
           match uu____179 with
           | FStar_Tactics_Result.Success (a,q) ->
               let uu____186 = t2 a  in run uu____186 q
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed (msg, q))
  
let (get : FStar_Tactics_Types.proofstate tac) =
  mk_tac (fun p  -> FStar_Tactics_Result.Success (p, p)) 
let (idtac : unit tac) = ret () 
let (goal_to_string : FStar_Tactics_Types.goal -> Prims.string) =
  fun g  ->
    let g_binders =
      let uu____205 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      FStar_All.pipe_right uu____205
        (FStar_Syntax_Print.binders_to_string ", ")
       in
    let w = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.witness
       in
    let t = bnorm g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
       in
    let uu____208 = tts g.FStar_Tactics_Types.context w  in
    let uu____209 = tts g.FStar_Tactics_Types.context t  in
    FStar_Util.format3 "%s |- %s : %s" g_binders uu____208 uu____209
  
let (tacprint : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "TAC>> %s\n" s 
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      let uu____225 = FStar_Util.format1 s x  in
      FStar_Util.print1 "TAC>> %s\n" uu____225
  
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        let uu____241 = FStar_Util.format2 s x y  in
        FStar_Util.print1 "TAC>> %s\n" uu____241
  
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____262 = FStar_Util.format3 s x y z  in
          FStar_Util.print1 "TAC>> %s\n" uu____262
  
let (comp_to_typ : FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____269) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____279) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (is_irrelevant : FStar_Tactics_Types.goal -> Prims.bool) =
  fun g  ->
    let uu____294 =
      let uu____299 =
        FStar_TypeChecker_Normalize.unfold_whnf g.FStar_Tactics_Types.context
          g.FStar_Tactics_Types.goal_ty
         in
      FStar_Syntax_Util.un_squash uu____299  in
    match uu____294 with
    | FStar_Pervasives_Native.Some t -> true
    | uu____305 -> false
  
let (print : Prims.string -> unit tac) = fun msg  -> tacprint msg; ret () 
let (debug : Prims.string -> unit tac) =
  fun msg  ->
    bind get
      (fun ps  ->
         (let uu____333 =
            let uu____334 =
              FStar_Ident.string_of_lid
                (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.curmodule
               in
            FStar_Options.debug_module uu____334  in
          if uu____333 then tacprint msg else ());
         ret ())
  
let dump_goal : 'Auu____342 . 'Auu____342 -> FStar_Tactics_Types.goal -> unit
  =
  fun ps  ->
    fun goal  -> let uu____354 = goal_to_string goal  in tacprint uu____354
  
let (dump_cur : FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      match ps.FStar_Tactics_Types.goals with
      | [] -> tacprint1 "No more goals (%s)" msg
      | h::uu____366 ->
          (tacprint1 "Current goal (%s):" msg;
           (let uu____370 = FStar_List.hd ps.FStar_Tactics_Types.goals  in
            dump_goal ps uu____370))
  
let (ps_to_string :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu____379  ->
    match uu____379 with
    | (msg,ps) ->
        let uu____386 =
          let uu____389 =
            let uu____390 =
              FStar_Util.string_of_int ps.FStar_Tactics_Types.depth  in
            FStar_Util.format2 "State dump @ depth %s (%s):\n" uu____390 msg
             in
          let uu____391 =
            let uu____394 =
              let uu____395 =
                FStar_Range.string_of_range
                  ps.FStar_Tactics_Types.entry_range
                 in
              FStar_Util.format1 "Location: %s\n" uu____395  in
            let uu____396 =
              let uu____399 =
                let uu____400 =
                  FStar_Util.string_of_int
                    (FStar_List.length ps.FStar_Tactics_Types.goals)
                   in
                let uu____401 =
                  let uu____402 =
                    FStar_List.map goal_to_string
                      ps.FStar_Tactics_Types.goals
                     in
                  FStar_String.concat "\n" uu____402  in
                FStar_Util.format2 "ACTIVE goals (%s):\n%s\n" uu____400
                  uu____401
                 in
              let uu____405 =
                let uu____408 =
                  let uu____409 =
                    FStar_Util.string_of_int
                      (FStar_List.length ps.FStar_Tactics_Types.smt_goals)
                     in
                  let uu____410 =
                    let uu____411 =
                      FStar_List.map goal_to_string
                        ps.FStar_Tactics_Types.smt_goals
                       in
                    FStar_String.concat "\n" uu____411  in
                  FStar_Util.format2 "SMT goals (%s):\n%s\n" uu____409
                    uu____410
                   in
                [uu____408]  in
              uu____399 :: uu____405  in
            uu____394 :: uu____396  in
          uu____389 :: uu____391  in
        FStar_String.concat "" uu____386
  
let (goal_to_json : FStar_Tactics_Types.goal -> FStar_Util.json) =
  fun g  ->
    let g_binders =
      let uu____420 =
        FStar_TypeChecker_Env.all_binders g.FStar_Tactics_Types.context  in
      let uu____421 =
        let uu____426 =
          FStar_TypeChecker_Env.dsenv g.FStar_Tactics_Types.context  in
        FStar_Syntax_Print.binders_to_json uu____426  in
      FStar_All.pipe_right uu____420 uu____421  in
    let uu____427 =
      let uu____434 =
        let uu____441 =
          let uu____446 =
            let uu____447 =
              let uu____454 =
                let uu____459 =
                  let uu____460 =
                    tts g.FStar_Tactics_Types.context
                      g.FStar_Tactics_Types.witness
                     in
                  FStar_Util.JsonStr uu____460  in
                ("witness", uu____459)  in
              let uu____461 =
                let uu____468 =
                  let uu____473 =
                    let uu____474 =
                      tts g.FStar_Tactics_Types.context
                        g.FStar_Tactics_Types.goal_ty
                       in
                    FStar_Util.JsonStr uu____474  in
                  ("type", uu____473)  in
                [uu____468]  in
              uu____454 :: uu____461  in
            FStar_Util.JsonAssoc uu____447  in
          ("goal", uu____446)  in
        [uu____441]  in
      ("hyps", g_binders) :: uu____434  in
    FStar_Util.JsonAssoc uu____427
  
let (ps_to_json :
  (Prims.string,FStar_Tactics_Types.proofstate)
    FStar_Pervasives_Native.tuple2 -> FStar_Util.json)
  =
  fun uu____507  ->
    match uu____507 with
    | (msg,ps) ->
        let uu____514 =
          let uu____521 =
            let uu____528 =
              let uu____535 =
                let uu____542 =
                  let uu____547 =
                    let uu____548 =
                      FStar_List.map goal_to_json
                        ps.FStar_Tactics_Types.goals
                       in
                    FStar_Util.JsonList uu____548  in
                  ("goals", uu____547)  in
                let uu____551 =
                  let uu____558 =
                    let uu____563 =
                      let uu____564 =
                        FStar_List.map goal_to_json
                          ps.FStar_Tactics_Types.smt_goals
                         in
                      FStar_Util.JsonList uu____564  in
                    ("smt-goals", uu____563)  in
                  [uu____558]  in
                uu____542 :: uu____551  in
              ("depth", (FStar_Util.JsonInt (ps.FStar_Tactics_Types.depth)))
                :: uu____535
               in
            ("label", (FStar_Util.JsonStr msg)) :: uu____528  in
          let uu____587 =
            if ps.FStar_Tactics_Types.entry_range <> FStar_Range.dummyRange
            then
              let uu____600 =
                let uu____605 =
                  FStar_Range.json_of_def_range
                    ps.FStar_Tactics_Types.entry_range
                   in
                ("location", uu____605)  in
              [uu____600]
            else []  in
          FStar_List.append uu____521 uu____587  in
        FStar_Util.JsonAssoc uu____514
  
let (dump_proofstate :
  FStar_Tactics_Types.proofstate -> Prims.string -> unit) =
  fun ps  ->
    fun msg  ->
      FStar_Options.with_saved_options
        (fun uu____635  ->
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
         (let uu____658 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_cur uu____658 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (print_proof_state : Prims.string -> unit tac) =
  fun msg  ->
    mk_tac
      (fun ps  ->
         let psc = ps.FStar_Tactics_Types.psc  in
         let subst1 = FStar_TypeChecker_Normalize.psc_subst psc  in
         (let uu____676 = FStar_Tactics_Types.subst_proof_state subst1 ps  in
          dump_proofstate uu____676 msg);
         FStar_Tactics_Result.Success ((), ps))
  
let (tac_verb_dbg : Prims.bool FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let rec (log : FStar_Tactics_Types.proofstate -> (unit -> unit) -> unit) =
  fun ps  ->
    fun f  ->
      let uu____709 = FStar_ST.op_Bang tac_verb_dbg  in
      match uu____709 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____740 =
              let uu____743 =
                FStar_TypeChecker_Env.debug
                  ps.FStar_Tactics_Types.main_context
                  (FStar_Options.Other "TacVerbose")
                 in
              FStar_Pervasives_Native.Some uu____743  in
            FStar_ST.op_Colon_Equals tac_verb_dbg uu____740);
           log ps f)
      | FStar_Pervasives_Native.Some (true ) -> f ()
      | FStar_Pervasives_Native.Some (false ) -> ()
  
let mlog : 'a . (unit -> unit) -> (unit -> 'a tac) -> 'a tac =
  fun f  -> fun cont  -> bind get (fun ps  -> log ps f; cont ()) 
let fail : 'a . Prims.string -> 'a tac =
  fun msg  ->
    mk_tac
      (fun ps  ->
         (let uu____824 =
            FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
              (FStar_Options.Other "TacFail")
             in
          if uu____824
          then dump_proofstate ps (Prims.strcat "TACTIC FAILING: " msg)
          else ());
         FStar_Tactics_Result.Failed (msg, ps))
  
let fail1 : 'Auu____832 . Prims.string -> Prims.string -> 'Auu____832 tac =
  fun msg  ->
    fun x  -> let uu____845 = FStar_Util.format1 msg x  in fail uu____845
  
let fail2 :
  'Auu____854 .
    Prims.string -> Prims.string -> Prims.string -> 'Auu____854 tac
  =
  fun msg  ->
    fun x  ->
      fun y  -> let uu____872 = FStar_Util.format2 msg x y  in fail uu____872
  
let fail3 :
  'Auu____883 .
    Prims.string ->
      Prims.string -> Prims.string -> Prims.string -> 'Auu____883 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          let uu____906 = FStar_Util.format3 msg x y z  in fail uu____906
  
let fail4 :
  'Auu____919 .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> Prims.string -> 'Auu____919 tac
  =
  fun msg  ->
    fun x  ->
      fun y  ->
        fun z  ->
          fun w  ->
            let uu____947 = FStar_Util.format4 msg x y z w  in fail uu____947
  
let trytac' : 'a . 'a tac -> (Prims.string,'a) FStar_Util.either tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         let uu____980 = run t ps  in
         match uu____980 with
         | FStar_Tactics_Result.Success (a,q) ->
             (FStar_Syntax_Unionfind.commit tx;
              FStar_Tactics_Result.Success ((FStar_Util.Inr a), q))
         | FStar_Tactics_Result.Failed (m,q) ->
             (FStar_Syntax_Unionfind.rollback tx;
              (let ps1 =
                 let uu___89_1004 = ps  in
                 {
                   FStar_Tactics_Types.main_context =
                     (uu___89_1004.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.main_goal =
                     (uu___89_1004.FStar_Tactics_Types.main_goal);
                   FStar_Tactics_Types.all_implicits =
                     (uu___89_1004.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals =
                     (uu___89_1004.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (uu___89_1004.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth =
                     (uu___89_1004.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (uu___89_1004.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc =
                     (uu___89_1004.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (uu___89_1004.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (uu___89_1004.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (q.FStar_Tactics_Types.freshness)
                 }  in
               FStar_Tactics_Result.Success ((FStar_Util.Inl m), ps1))))
  
let trytac : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    let uu____1031 = trytac' t  in
    bind uu____1031
      (fun r  ->
         match r with
         | FStar_Util.Inr v1 -> ret (FStar_Pervasives_Native.Some v1)
         | FStar_Util.Inl uu____1058 -> ret FStar_Pervasives_Native.None)
  
let trytac_exn : 'a . 'a tac -> 'a FStar_Pervasives_Native.option tac =
  fun t  ->
    mk_tac
      (fun ps  ->
         try let uu____1094 = trytac t  in run uu____1094 ps
         with
         | FStar_Errors.Err (uu____1110,msg) ->
             (log ps
                (fun uu____1114  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps))
         | FStar_Errors.Error (uu____1119,msg,uu____1121) ->
             (log ps
                (fun uu____1124  ->
                   FStar_Util.print1 "trytac_exn error: (%s)" msg);
              FStar_Tactics_Result.Success (FStar_Pervasives_Native.None, ps)))
  
let wrap_err : 'a . Prims.string -> 'a tac -> 'a tac =
  fun pref  ->
    fun t  ->
      mk_tac
        (fun ps  ->
           let uu____1157 = run t ps  in
           match uu____1157 with
           | FStar_Tactics_Result.Success (a,q) ->
               FStar_Tactics_Result.Success (a, q)
           | FStar_Tactics_Result.Failed (msg,q) ->
               FStar_Tactics_Result.Failed
                 ((Prims.strcat pref (Prims.strcat ": " msg)), q))
  
let (set : FStar_Tactics_Types.proofstate -> unit tac) =
  fun p  -> mk_tac (fun uu____1176  -> FStar_Tactics_Result.Success ((), p)) 
let (__do_unify :
  env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____1197 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")  in
         if uu____1197
         then
           let uu____1198 = FStar_Syntax_Print.term_to_string t1  in
           let uu____1199 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "%%%%%%%%do_unify %s =? %s\n" uu____1198
             uu____1199
         else ());
        (try
           let res = FStar_TypeChecker_Rel.teq_nosmt env t1 t2  in
           (let uu____1211 =
              FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
               in
            if uu____1211
            then
              let uu____1212 = FStar_Util.string_of_bool res  in
              let uu____1213 = FStar_Syntax_Print.term_to_string t1  in
              let uu____1214 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print3 "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                uu____1212 uu____1213 uu____1214
            else ());
           ret res
         with
         | FStar_Errors.Err (uu____1222,msg) ->
             mlog
               (fun uu____1225  ->
                  FStar_Util.print1 ">> do_unify error, (%s)\n" msg)
               (fun uu____1227  -> ret false)
         | FStar_Errors.Error (uu____1228,msg,r) ->
             mlog
               (fun uu____1233  ->
                  let uu____1234 = FStar_Range.string_of_range r  in
                  FStar_Util.print2 ">> do_unify error, (%s) at (%s)\n" msg
                    uu____1234) (fun uu____1236  -> ret false))
  
let (do_unify :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool tac)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        bind idtac
          (fun uu____1259  ->
             (let uu____1261 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "1346")
                 in
              if uu____1261
              then
                (FStar_Options.push ();
                 (let uu____1263 =
                    FStar_Options.set_options FStar_Options.Set
                      "--debug_level Rel --debug_level RelCheck"
                     in
                  ()))
              else ());
             (let uu____1265 =
                let uu____1268 = __do_unify env t1 t2  in
                bind uu____1268
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
              bind uu____1265
                (fun r  ->
                   (let uu____1284 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "1346")
                       in
                    if uu____1284 then FStar_Options.pop () else ());
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
       let uu____1305 =
         let uu___94_1306 = p  in
         let uu____1307 = FStar_List.tl p.FStar_Tactics_Types.goals  in
         {
           FStar_Tactics_Types.main_context =
             (uu___94_1306.FStar_Tactics_Types.main_context);
           FStar_Tactics_Types.main_goal =
             (uu___94_1306.FStar_Tactics_Types.main_goal);
           FStar_Tactics_Types.all_implicits =
             (uu___94_1306.FStar_Tactics_Types.all_implicits);
           FStar_Tactics_Types.goals = uu____1307;
           FStar_Tactics_Types.smt_goals =
             (uu___94_1306.FStar_Tactics_Types.smt_goals);
           FStar_Tactics_Types.depth =
             (uu___94_1306.FStar_Tactics_Types.depth);
           FStar_Tactics_Types.__dump =
             (uu___94_1306.FStar_Tactics_Types.__dump);
           FStar_Tactics_Types.psc = (uu___94_1306.FStar_Tactics_Types.psc);
           FStar_Tactics_Types.entry_range =
             (uu___94_1306.FStar_Tactics_Types.entry_range);
           FStar_Tactics_Types.guard_policy =
             (uu___94_1306.FStar_Tactics_Types.guard_policy);
           FStar_Tactics_Types.freshness =
             (uu___94_1306.FStar_Tactics_Types.freshness)
         }  in
       set uu____1305)
  
let (dismiss : unit -> unit tac) =
  fun uu____1316  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "dismiss: no more goals"
         | uu____1323 -> __dismiss)
  
let (solve :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.term -> unit tac) =
  fun goal  ->
    fun solution  ->
      let e = goal.FStar_Tactics_Types.context  in
      mlog
        (fun uu____1344  ->
           let uu____1345 = tts e goal.FStar_Tactics_Types.witness  in
           let uu____1346 = tts e solution  in
           FStar_Util.print2 "solve %s := %s\n" uu____1345 uu____1346)
        (fun uu____1349  ->
           let uu____1350 = trysolve goal solution  in
           bind uu____1350
             (fun b  ->
                if b
                then __dismiss
                else
                  (let uu____1358 =
                     let uu____1359 =
                       tts goal.FStar_Tactics_Types.context solution  in
                     let uu____1360 =
                       tts goal.FStar_Tactics_Types.context
                         goal.FStar_Tactics_Types.witness
                        in
                     let uu____1361 =
                       tts goal.FStar_Tactics_Types.context
                         goal.FStar_Tactics_Types.goal_ty
                        in
                     FStar_Util.format3 "%s does not solve %s : %s"
                       uu____1359 uu____1360 uu____1361
                      in
                   fail uu____1358)))
  
let (dismiss_all : unit tac) =
  bind get
    (fun p  ->
       set
         (let uu___95_1368 = p  in
          {
            FStar_Tactics_Types.main_context =
              (uu___95_1368.FStar_Tactics_Types.main_context);
            FStar_Tactics_Types.main_goal =
              (uu___95_1368.FStar_Tactics_Types.main_goal);
            FStar_Tactics_Types.all_implicits =
              (uu___95_1368.FStar_Tactics_Types.all_implicits);
            FStar_Tactics_Types.goals = [];
            FStar_Tactics_Types.smt_goals =
              (uu___95_1368.FStar_Tactics_Types.smt_goals);
            FStar_Tactics_Types.depth =
              (uu___95_1368.FStar_Tactics_Types.depth);
            FStar_Tactics_Types.__dump =
              (uu___95_1368.FStar_Tactics_Types.__dump);
            FStar_Tactics_Types.psc = (uu___95_1368.FStar_Tactics_Types.psc);
            FStar_Tactics_Types.entry_range =
              (uu___95_1368.FStar_Tactics_Types.entry_range);
            FStar_Tactics_Types.guard_policy =
              (uu___95_1368.FStar_Tactics_Types.guard_policy);
            FStar_Tactics_Types.freshness =
              (uu___95_1368.FStar_Tactics_Types.freshness)
          }))
  
let (nwarn : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (check_valid_goal : FStar_Tactics_Types.goal -> unit) =
  fun g  ->
    let uu____1387 = FStar_Options.defensive ()  in
    if uu____1387
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
        let uu____1403 = FStar_TypeChecker_Env.pop_bv e  in
        match uu____1403 with
        | FStar_Pervasives_Native.None  -> b3
        | FStar_Pervasives_Native.Some (bv,e1) ->
            let b4 =
              b3 &&
                (FStar_TypeChecker_Env.closed e1 bv.FStar_Syntax_Syntax.sort)
               in
            aux b4 e1
         in
      let uu____1421 =
        (let uu____1424 = aux b2 env  in Prims.op_Negation uu____1424) &&
          (let uu____1426 = FStar_ST.op_Bang nwarn  in
           uu____1426 < (Prims.parse_int "5"))
         in
      (if uu____1421
       then
         ((let uu____1451 =
             let uu____1456 =
               let uu____1457 = goal_to_string g  in
               FStar_Util.format1
                 "The following goal is ill-formed. Keeping calm and carrying on...\n<%s>\n\n"
                 uu____1457
                in
             (FStar_Errors.Warning_IllFormedGoal, uu____1456)  in
           FStar_Errors.log_issue
             (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
             uu____1451);
          (let uu____1458 =
             let uu____1459 = FStar_ST.op_Bang nwarn  in
             uu____1459 + (Prims.parse_int "1")  in
           FStar_ST.op_Colon_Equals nwarn uu____1458))
       else ())
    else ()
  
let (add_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___96_1527 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___96_1527.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___96_1527.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___96_1527.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append gs p.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___96_1527.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___96_1527.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___96_1527.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___96_1527.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___96_1527.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___96_1527.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___96_1527.FStar_Tactics_Types.freshness)
            }))
  
let (add_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___97_1547 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___97_1547.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___97_1547.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___97_1547.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___97_1547.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append gs p.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___97_1547.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___97_1547.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___97_1547.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___97_1547.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___97_1547.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___97_1547.FStar_Tactics_Types.freshness)
            }))
  
let (push_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___98_1567 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___98_1567.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___98_1567.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___98_1567.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (FStar_List.append p.FStar_Tactics_Types.goals gs);
              FStar_Tactics_Types.smt_goals =
                (uu___98_1567.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___98_1567.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___98_1567.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___98_1567.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___98_1567.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___98_1567.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___98_1567.FStar_Tactics_Types.freshness)
            }))
  
let (push_smt_goals : FStar_Tactics_Types.goal Prims.list -> unit tac) =
  fun gs  ->
    bind get
      (fun p  ->
         FStar_List.iter check_valid_goal gs;
         set
           (let uu___99_1587 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___99_1587.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___99_1587.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___99_1587.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___99_1587.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (FStar_List.append p.FStar_Tactics_Types.smt_goals gs);
              FStar_Tactics_Types.depth =
                (uu___99_1587.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___99_1587.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___99_1587.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___99_1587.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___99_1587.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___99_1587.FStar_Tactics_Types.freshness)
            }))
  
let (replace_cur : FStar_Tactics_Types.goal -> unit tac) =
  fun g  -> bind __dismiss (fun uu____1598  -> add_goals [g]) 
let (add_implicits : implicits -> unit tac) =
  fun i  ->
    bind get
      (fun p  ->
         set
           (let uu___100_1612 = p  in
            {
              FStar_Tactics_Types.main_context =
                (uu___100_1612.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___100_1612.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (FStar_List.append i p.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___100_1612.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___100_1612.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___100_1612.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___100_1612.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___100_1612.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___100_1612.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy =
                (uu___100_1612.FStar_Tactics_Types.guard_policy);
              FStar_Tactics_Types.freshness =
                (uu___100_1612.FStar_Tactics_Types.freshness)
            }))
  
let (new_uvar :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Syntax_Syntax.term tac)
  =
  fun reason  ->
    fun env  ->
      fun typ  ->
        let uu____1644 =
          FStar_TypeChecker_Util.new_implicit_var reason
            typ.FStar_Syntax_Syntax.pos env typ
           in
        match uu____1644 with
        | (u,uu____1660,g_u) ->
            let uu____1674 =
              add_implicits g_u.FStar_TypeChecker_Env.implicits  in
            bind uu____1674 (fun uu____1678  -> ret u)
  
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1684 = FStar_Syntax_Util.un_squash t  in
    match uu____1684 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1694 =
          let uu____1695 = FStar_Syntax_Subst.compress t'  in
          uu____1695.FStar_Syntax_Syntax.n  in
        (match uu____1694 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu____1699 -> false)
    | uu____1700 -> false
  
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____1710 = FStar_Syntax_Util.un_squash t  in
    match uu____1710 with
    | FStar_Pervasives_Native.Some t' ->
        let uu____1720 =
          let uu____1721 = FStar_Syntax_Subst.compress t'  in
          uu____1721.FStar_Syntax_Syntax.n  in
        (match uu____1720 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu____1725 -> false)
    | uu____1726 -> false
  
let (cur_goal : unit -> FStar_Tactics_Types.goal tac) =
  fun uu____1737  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> fail "No more goals (1)"
         | hd1::tl1 -> ret hd1)
  
let (tadmit : unit -> unit tac) =
  fun uu____1754  ->
    let uu____1757 =
      let uu____1760 = cur_goal ()  in
      bind uu____1760
        (fun g  ->
           (let uu____1767 =
              let uu____1772 =
                let uu____1773 = goal_to_string g  in
                FStar_Util.format1 "Tactics admitted goal <%s>\n\n"
                  uu____1773
                 in
              (FStar_Errors.Warning_TacAdmit, uu____1772)  in
            FStar_Errors.log_issue
              (g.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
              uu____1767);
           solve g FStar_Syntax_Util.exp_unit)
       in
    FStar_All.pipe_left (wrap_err "tadmit") uu____1757
  
let (fresh : unit -> FStar_BigInt.t tac) =
  fun uu____1784  ->
    bind get
      (fun ps  ->
         let n1 = ps.FStar_Tactics_Types.freshness  in
         let ps1 =
           let uu___101_1794 = ps  in
           {
             FStar_Tactics_Types.main_context =
               (uu___101_1794.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.main_goal =
               (uu___101_1794.FStar_Tactics_Types.main_goal);
             FStar_Tactics_Types.all_implicits =
               (uu___101_1794.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals =
               (uu___101_1794.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (uu___101_1794.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth =
               (uu___101_1794.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump =
               (uu___101_1794.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc =
               (uu___101_1794.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (uu___101_1794.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (uu___101_1794.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n1 + (Prims.parse_int "1"))
           }  in
         let uu____1795 = set ps1  in
         bind uu____1795
           (fun uu____1800  ->
              let uu____1801 = FStar_BigInt.of_int_fs n1  in ret uu____1801))
  
let (ngoals : unit -> FStar_BigInt.t tac) =
  fun uu____1808  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.goals  in
         let uu____1816 = FStar_BigInt.of_int_fs n1  in ret uu____1816)
  
let (ngoals_smt : unit -> FStar_BigInt.t tac) =
  fun uu____1829  ->
    bind get
      (fun ps  ->
         let n1 = FStar_List.length ps.FStar_Tactics_Types.smt_goals  in
         let uu____1837 = FStar_BigInt.of_int_fs n1  in ret uu____1837)
  
let (is_guard : unit -> Prims.bool tac) =
  fun uu____1850  ->
    let uu____1853 = cur_goal ()  in
    bind uu____1853 (fun g  -> ret g.FStar_Tactics_Types.is_guard)
  
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
            let uu____1885 = env.FStar_TypeChecker_Env.universe_of env phi
               in
            FStar_Syntax_Util.mk_squash uu____1885 phi  in
          let uu____1886 = new_uvar reason env typ  in
          bind uu____1886
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
             (fun uu____1935  ->
                let uu____1936 = tts e t  in
                FStar_Util.print1 "Tac> __tc(%s)\n" uu____1936)
             (fun uu____1938  ->
                try
                  let uu____1958 =
                    (ps.FStar_Tactics_Types.main_context).FStar_TypeChecker_Env.type_of
                      e t
                     in
                  ret uu____1958
                with
                | FStar_Errors.Err (uu____1985,msg) ->
                    let uu____1987 = tts e t  in
                    let uu____1988 =
                      let uu____1989 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____1989
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1987 uu____1988 msg
                | FStar_Errors.Error (uu____1996,msg,uu____1998) ->
                    let uu____1999 = tts e t  in
                    let uu____2000 =
                      let uu____2001 = FStar_TypeChecker_Env.all_binders e
                         in
                      FStar_All.pipe_right uu____2001
                        (FStar_Syntax_Print.binders_to_string ", ")
                       in
                    fail3 "Cannot type %s in context (%s). Error = (%s)"
                      uu____1999 uu____2000 msg))
  
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
  fun uu____2028  ->
    bind get (fun ps  -> ret ps.FStar_Tactics_Types.guard_policy)
  
let (set_guard_policy : FStar_Tactics_Types.guard_policy -> unit tac) =
  fun pol  ->
    bind get
      (fun ps  ->
         set
           (let uu___104_2046 = ps  in
            {
              FStar_Tactics_Types.main_context =
                (uu___104_2046.FStar_Tactics_Types.main_context);
              FStar_Tactics_Types.main_goal =
                (uu___104_2046.FStar_Tactics_Types.main_goal);
              FStar_Tactics_Types.all_implicits =
                (uu___104_2046.FStar_Tactics_Types.all_implicits);
              FStar_Tactics_Types.goals =
                (uu___104_2046.FStar_Tactics_Types.goals);
              FStar_Tactics_Types.smt_goals =
                (uu___104_2046.FStar_Tactics_Types.smt_goals);
              FStar_Tactics_Types.depth =
                (uu___104_2046.FStar_Tactics_Types.depth);
              FStar_Tactics_Types.__dump =
                (uu___104_2046.FStar_Tactics_Types.__dump);
              FStar_Tactics_Types.psc =
                (uu___104_2046.FStar_Tactics_Types.psc);
              FStar_Tactics_Types.entry_range =
                (uu___104_2046.FStar_Tactics_Types.entry_range);
              FStar_Tactics_Types.guard_policy = pol;
              FStar_Tactics_Types.freshness =
                (uu___104_2046.FStar_Tactics_Types.freshness)
            }))
  
let with_policy : 'a . FStar_Tactics_Types.guard_policy -> 'a tac -> 'a tac =
  fun pol  ->
    fun t  ->
      let uu____2070 = get_guard_policy ()  in
      bind uu____2070
        (fun old_pol  ->
           let uu____2076 = set_guard_policy pol  in
           bind uu____2076
             (fun uu____2080  ->
                bind t
                  (fun r  ->
                     let uu____2084 = set_guard_policy old_pol  in
                     bind uu____2084 (fun uu____2088  -> ret r))))
  
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Env.guard_t -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun e  ->
      fun g  ->
        fun opts  ->
          let uu____2113 =
            let uu____2114 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2114.FStar_TypeChecker_Env.guard_f  in
          match uu____2113 with
          | FStar_TypeChecker_Common.Trivial  -> ret ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2118 = istrivial e f  in
              if uu____2118
              then ret ()
              else
                bind get
                  (fun ps  ->
                     match ps.FStar_Tactics_Types.guard_policy with
                     | FStar_Tactics_Types.Drop  -> ret ()
                     | FStar_Tactics_Types.Goal  ->
                         let uu____2126 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2126
                           (fun goal  ->
                              let goal1 =
                                let uu___105_2133 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___105_2133.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___105_2133.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___105_2133.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___105_2133.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_goals [goal1])
                     | FStar_Tactics_Types.SMT  ->
                         let uu____2134 = mk_irrelevant_goal reason e f opts
                            in
                         bind uu____2134
                           (fun goal  ->
                              let goal1 =
                                let uu___106_2141 = goal  in
                                {
                                  FStar_Tactics_Types.context =
                                    (uu___106_2141.FStar_Tactics_Types.context);
                                  FStar_Tactics_Types.witness =
                                    (uu___106_2141.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___106_2141.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___106_2141.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard = true
                                }  in
                              push_smt_goals [goal1])
                     | FStar_Tactics_Types.Force  ->
                         (try
                            let uu____2149 =
                              let uu____2150 =
                                let uu____2151 =
                                  FStar_TypeChecker_Rel.discharge_guard_no_smt
                                    e g
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Rel.is_trivial uu____2151
                                 in
                              Prims.op_Negation uu____2150  in
                            if uu____2149
                            then
                              mlog
                                (fun uu____2156  ->
                                   let uu____2157 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2157)
                                (fun uu____2159  ->
                                   fail1 "Forcing the guard failed %s)"
                                     reason)
                            else ret ()
                          with
                          | uu____2166 ->
                              mlog
                                (fun uu____2169  ->
                                   let uu____2170 =
                                     FStar_TypeChecker_Rel.guard_to_string e
                                       g
                                      in
                                   FStar_Util.print1 "guard = %s\n"
                                     uu____2170)
                                (fun uu____2172  ->
                                   fail1 "Forcing the guard failed (%s)"
                                     reason)))
  
let (tc : FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ tac) =
  fun t  ->
    let uu____2182 =
      let uu____2185 = cur_goal ()  in
      bind uu____2185
        (fun goal  ->
           let uu____2191 = __tc goal.FStar_Tactics_Types.context t  in
           bind uu____2191
             (fun uu____2211  ->
                match uu____2211 with
                | (t1,typ,guard) ->
                    let uu____2223 =
                      proc_guard "tc" goal.FStar_Tactics_Types.context guard
                        goal.FStar_Tactics_Types.opts
                       in
                    bind uu____2223 (fun uu____2227  -> ret typ)))
       in
    FStar_All.pipe_left (wrap_err "tc") uu____2182
  
let (add_irrelevant_goal :
  Prims.string ->
    env -> FStar_Reflection_Data.typ -> FStar_Options.optionstate -> unit tac)
  =
  fun reason  ->
    fun env  ->
      fun phi  ->
        fun opts  ->
          let uu____2256 = mk_irrelevant_goal reason env phi opts  in
          bind uu____2256 (fun goal  -> add_goals [goal])
  
let (trivial : unit -> unit tac) =
  fun uu____2267  ->
    let uu____2270 = cur_goal ()  in
    bind uu____2270
      (fun goal  ->
         let uu____2276 =
           istrivial goal.FStar_Tactics_Types.context
             goal.FStar_Tactics_Types.goal_ty
            in
         if uu____2276
         then solve goal FStar_Syntax_Util.exp_unit
         else
           (let uu____2280 =
              tts goal.FStar_Tactics_Types.context
                goal.FStar_Tactics_Types.goal_ty
               in
            fail1 "Not a trivial goal: %s" uu____2280))
  
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
          let uu____2309 =
            let uu____2310 = FStar_TypeChecker_Rel.simplify_guard e g  in
            uu____2310.FStar_TypeChecker_Env.guard_f  in
          match uu____2309 with
          | FStar_TypeChecker_Common.Trivial  ->
              ret FStar_Pervasives_Native.None
          | FStar_TypeChecker_Common.NonTrivial f ->
              let uu____2318 = istrivial e f  in
              if uu____2318
              then ret FStar_Pervasives_Native.None
              else
                (let uu____2326 = mk_irrelevant_goal reason e f opts  in
                 bind uu____2326
                   (fun goal  ->
                      ret
                        (FStar_Pervasives_Native.Some
                           (let uu___109_2336 = goal  in
                            {
                              FStar_Tactics_Types.context =
                                (uu___109_2336.FStar_Tactics_Types.context);
                              FStar_Tactics_Types.witness =
                                (uu___109_2336.FStar_Tactics_Types.witness);
                              FStar_Tactics_Types.goal_ty =
                                (uu___109_2336.FStar_Tactics_Types.goal_ty);
                              FStar_Tactics_Types.opts =
                                (uu___109_2336.FStar_Tactics_Types.opts);
                              FStar_Tactics_Types.is_guard = true
                            }))))
  
let (smt : unit -> unit tac) =
  fun uu____2343  ->
    let uu____2346 = cur_goal ()  in
    bind uu____2346
      (fun g  ->
         let uu____2352 = is_irrelevant g  in
         if uu____2352
         then bind __dismiss (fun uu____2356  -> add_smt_goals [g])
         else
           (let uu____2358 =
              tts g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
               in
            fail1 "goal is not irrelevant: cannot dispatch to smt (%s)"
              uu____2358))
  
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
             let uu____2407 =
               try
                 let uu____2441 =
                   let uu____2450 = FStar_BigInt.to_int_fs n1  in
                   FStar_List.splitAt uu____2450 p.FStar_Tactics_Types.goals
                    in
                 ret uu____2441
               with | uu____2472 -> fail "divide: not enough goals"  in
             bind uu____2407
               (fun uu____2499  ->
                  match uu____2499 with
                  | (lgs,rgs) ->
                      let lp =
                        let uu___110_2525 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___110_2525.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___110_2525.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___110_2525.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___110_2525.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___110_2525.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___110_2525.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___110_2525.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___110_2525.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___110_2525.FStar_Tactics_Types.freshness)
                        }  in
                      let rp =
                        let uu___111_2527 = p  in
                        {
                          FStar_Tactics_Types.main_context =
                            (uu___111_2527.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.main_goal =
                            (uu___111_2527.FStar_Tactics_Types.main_goal);
                          FStar_Tactics_Types.all_implicits =
                            (uu___111_2527.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = rgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (uu___111_2527.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (uu___111_2527.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (uu___111_2527.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (uu___111_2527.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (uu___111_2527.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (uu___111_2527.FStar_Tactics_Types.freshness)
                        }  in
                      let uu____2528 = set lp  in
                      bind uu____2528
                        (fun uu____2536  ->
                           bind l
                             (fun a  ->
                                bind get
                                  (fun lp'  ->
                                     let uu____2550 = set rp  in
                                     bind uu____2550
                                       (fun uu____2558  ->
                                          bind r
                                            (fun b  ->
                                               bind get
                                                 (fun rp'  ->
                                                    let p' =
                                                      let uu___112_2574 = p
                                                         in
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.main_goal
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.main_goal);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.all_implicits);
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
                                                          (uu___112_2574.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (uu___112_2574.FStar_Tactics_Types.freshness)
                                                      }  in
                                                    let uu____2575 = set p'
                                                       in
                                                    bind uu____2575
                                                      (fun uu____2583  ->
                                                         ret (a, b))))))))))
  
let focus : 'a . 'a tac -> 'a tac =
  fun f  ->
    let uu____2604 = divide FStar_BigInt.one f idtac  in
    bind uu____2604
      (fun uu____2617  -> match uu____2617 with | (a,()) -> ret a)
  
let rec map : 'a . 'a tac -> 'a Prims.list tac =
  fun tau  ->
    bind get
      (fun p  ->
         match p.FStar_Tactics_Types.goals with
         | [] -> ret []
         | uu____2654::uu____2655 ->
             let uu____2658 =
               let uu____2667 = map tau  in
               divide FStar_BigInt.one tau uu____2667  in
             bind uu____2658
               (fun uu____2685  ->
                  match uu____2685 with | (h,t) -> ret (h :: t)))
  
let (seq : unit tac -> unit tac -> unit tac) =
  fun t1  ->
    fun t2  ->
      let uu____2726 =
        bind t1
          (fun uu____2731  ->
             let uu____2732 = map t2  in
             bind uu____2732 (fun uu____2740  -> ret ()))
         in
      focus uu____2726
  
let (intro : unit -> FStar_Syntax_Syntax.binder tac) =
  fun uu____2749  ->
    let uu____2752 =
      let uu____2755 = cur_goal ()  in
      bind uu____2755
        (fun goal  ->
           let uu____2764 =
             FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
           match uu____2764 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____2779 =
                 let uu____2780 = FStar_Syntax_Util.is_total_comp c  in
                 Prims.op_Negation uu____2780  in
               if uu____2779
               then fail "Codomain is effectful"
               else
                 (let env' =
                    FStar_TypeChecker_Env.push_binders
                      goal.FStar_Tactics_Types.context [b]
                     in
                  let typ' = comp_to_typ c  in
                  let uu____2786 = new_uvar "intro" env' typ'  in
                  bind uu____2786
                    (fun u  ->
                       let uu____2792 =
                         let uu____2795 =
                           FStar_Syntax_Util.abs [b] u
                             FStar_Pervasives_Native.None
                            in
                         trysolve goal uu____2795  in
                       bind uu____2792
                         (fun bb  ->
                            if bb
                            then
                              let uu____2801 =
                                let uu____2804 =
                                  let uu___115_2805 = goal  in
                                  let uu____2806 = bnorm env' u  in
                                  let uu____2807 = bnorm env' typ'  in
                                  {
                                    FStar_Tactics_Types.context = env';
                                    FStar_Tactics_Types.witness = uu____2806;
                                    FStar_Tactics_Types.goal_ty = uu____2807;
                                    FStar_Tactics_Types.opts =
                                      (uu___115_2805.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___115_2805.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____2804  in
                              bind uu____2801 (fun uu____2809  -> ret b)
                            else fail "unification failed")))
           | FStar_Pervasives_Native.None  ->
               let uu____2815 =
                 tts goal.FStar_Tactics_Types.context
                   goal.FStar_Tactics_Types.goal_ty
                  in
               fail1 "goal is not an arrow (%s)" uu____2815)
       in
    FStar_All.pipe_left (wrap_err "intro") uu____2752
  
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.binder)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun uu____2830  ->
    let uu____2837 = cur_goal ()  in
    bind uu____2837
      (fun goal  ->
         FStar_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu____2854 =
            FStar_Syntax_Util.arrow_one goal.FStar_Tactics_Types.goal_ty  in
          match uu____2854 with
          | FStar_Pervasives_Native.Some (b,c) ->
              let uu____2873 =
                let uu____2874 = FStar_Syntax_Util.is_total_comp c  in
                Prims.op_Negation uu____2874  in
              if uu____2873
              then fail "Codomain is effectful"
              else
                (let bv =
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None
                     goal.FStar_Tactics_Types.goal_ty
                    in
                 let bs =
                   let uu____2890 = FStar_Syntax_Syntax.mk_binder bv  in
                   [uu____2890; b]  in
                 let env' =
                   FStar_TypeChecker_Env.push_binders
                     goal.FStar_Tactics_Types.context bs
                    in
                 let uu____2892 =
                   let uu____2895 = comp_to_typ c  in
                   new_uvar "intro_rec" env' uu____2895  in
                 bind uu____2892
                   (fun u  ->
                      let lb =
                        let uu____2910 =
                          FStar_Syntax_Util.abs [b] u
                            FStar_Pervasives_Native.None
                           in
                        FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv)
                          [] goal.FStar_Tactics_Types.goal_ty
                          FStar_Parser_Const.effect_Tot_lid uu____2910 []
                          FStar_Range.dummyRange
                         in
                      let body = FStar_Syntax_Syntax.bv_to_name bv  in
                      let uu____2916 =
                        FStar_Syntax_Subst.close_let_rec [lb] body  in
                      match uu____2916 with
                      | (lbs,body1) ->
                          let tm =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_let
                                 ((true, lbs), body1))
                              FStar_Pervasives_Native.None
                              (goal.FStar_Tactics_Types.witness).FStar_Syntax_Syntax.pos
                             in
                          let uu____2946 = trysolve goal tm  in
                          bind uu____2946
                            (fun bb  ->
                               if bb
                               then
                                 let uu____2962 =
                                   let uu____2965 =
                                     let uu___116_2966 = goal  in
                                     let uu____2967 = bnorm env' u  in
                                     let uu____2968 =
                                       let uu____2969 = comp_to_typ c  in
                                       bnorm env' uu____2969  in
                                     {
                                       FStar_Tactics_Types.context = env';
                                       FStar_Tactics_Types.witness =
                                         uu____2967;
                                       FStar_Tactics_Types.goal_ty =
                                         uu____2968;
                                       FStar_Tactics_Types.opts =
                                         (uu___116_2966.FStar_Tactics_Types.opts);
                                       FStar_Tactics_Types.is_guard =
                                         (uu___116_2966.FStar_Tactics_Types.is_guard)
                                     }  in
                                   replace_cur uu____2965  in
                                 bind uu____2962
                                   (fun uu____2976  ->
                                      let uu____2977 =
                                        let uu____2982 =
                                          FStar_Syntax_Syntax.mk_binder bv
                                           in
                                        (uu____2982, b)  in
                                      ret uu____2977)
                               else fail "intro_rec: unification failed")))
          | FStar_Pervasives_Native.None  ->
              let uu____2996 =
                tts goal.FStar_Tactics_Types.context
                  goal.FStar_Tactics_Types.goal_ty
                 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu____2996))
  
let (norm : FStar_Syntax_Embeddings.norm_step Prims.list -> unit tac) =
  fun s  ->
    let uu____3014 = cur_goal ()  in
    bind uu____3014
      (fun goal  ->
         mlog
           (fun uu____3021  ->
              let uu____3022 =
                FStar_Syntax_Print.term_to_string
                  goal.FStar_Tactics_Types.witness
                 in
              FStar_Util.print1 "norm: witness = %s\n" uu____3022)
           (fun uu____3027  ->
              let steps =
                let uu____3031 = FStar_TypeChecker_Normalize.tr_norm_steps s
                   in
                FStar_List.append
                  [FStar_TypeChecker_Normalize.Reify;
                  FStar_TypeChecker_Normalize.UnfoldTac] uu____3031
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
                (let uu___117_3038 = goal  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___117_3038.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness = w;
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___117_3038.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___117_3038.FStar_Tactics_Types.is_guard)
                 })))
  
let (norm_term_env :
  env ->
    FStar_Syntax_Embeddings.norm_step Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun e  ->
    fun s  ->
      fun t  ->
        let uu____3062 =
          mlog
            (fun uu____3067  ->
               let uu____3068 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print1 "norm_term: tm = %s\n" uu____3068)
            (fun uu____3070  ->
               bind get
                 (fun ps  ->
                    let opts =
                      match ps.FStar_Tactics_Types.goals with
                      | g::uu____3076 -> g.FStar_Tactics_Types.opts
                      | uu____3079 -> FStar_Options.peek ()  in
                    mlog
                      (fun uu____3084  ->
                         let uu____3085 =
                           tts ps.FStar_Tactics_Types.main_context t  in
                         FStar_Util.print1 "norm_term_env: t = %s\n"
                           uu____3085)
                      (fun uu____3088  ->
                         let uu____3089 = __tc e t  in
                         bind uu____3089
                           (fun uu____3110  ->
                              match uu____3110 with
                              | (t1,uu____3120,uu____3121) ->
                                  let steps =
                                    let uu____3125 =
                                      FStar_TypeChecker_Normalize.tr_norm_steps
                                        s
                                       in
                                    FStar_List.append
                                      [FStar_TypeChecker_Normalize.Reify;
                                      FStar_TypeChecker_Normalize.UnfoldTac]
                                      uu____3125
                                     in
                                  let t2 =
                                    normalize steps
                                      ps.FStar_Tactics_Types.main_context t1
                                     in
                                  ret t2))))
           in
        FStar_All.pipe_left (wrap_err "norm_term") uu____3062
  
let (refine_intro : unit -> unit tac) =
  fun uu____3139  ->
    let uu____3142 =
      let uu____3145 = cur_goal ()  in
      bind uu____3145
        (fun g  ->
           let uu____3152 =
             FStar_TypeChecker_Rel.base_and_refinement
               g.FStar_Tactics_Types.context g.FStar_Tactics_Types.goal_ty
              in
           match uu____3152 with
           | (uu____3165,FStar_Pervasives_Native.None ) ->
               fail "not a refinement"
           | (t,FStar_Pervasives_Native.Some (bv,phi)) ->
               let g1 =
                 let uu___118_3190 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___118_3190.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___118_3190.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty = t;
                   FStar_Tactics_Types.opts =
                     (uu___118_3190.FStar_Tactics_Types.opts);
                   FStar_Tactics_Types.is_guard =
                     (uu___118_3190.FStar_Tactics_Types.is_guard)
                 }  in
               let uu____3191 =
                 let uu____3196 =
                   let uu____3201 =
                     let uu____3202 = FStar_Syntax_Syntax.mk_binder bv  in
                     [uu____3202]  in
                   FStar_Syntax_Subst.open_term uu____3201 phi  in
                 match uu____3196 with
                 | (bvs,phi1) ->
                     let uu____3209 =
                       let uu____3210 = FStar_List.hd bvs  in
                       FStar_Pervasives_Native.fst uu____3210  in
                     (uu____3209, phi1)
                  in
               (match uu____3191 with
                | (bv1,phi1) ->
                    let uu____3223 =
                      let uu____3226 =
                        FStar_Syntax_Subst.subst
                          [FStar_Syntax_Syntax.NT
                             (bv1, (g.FStar_Tactics_Types.witness))] phi1
                         in
                      mk_irrelevant_goal "refine_intro refinement"
                        g.FStar_Tactics_Types.context uu____3226
                        g.FStar_Tactics_Types.opts
                       in
                    bind uu____3223
                      (fun g2  ->
                         bind __dismiss
                           (fun uu____3230  -> add_goals [g1; g2]))))
       in
    FStar_All.pipe_left (wrap_err "refine_intro") uu____3142
  
let (__exact_now : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun t  ->
      let uu____3249 = cur_goal ()  in
      bind uu____3249
        (fun goal  ->
           let env =
             if set_expected_typ1
             then
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context
                 goal.FStar_Tactics_Types.goal_ty
             else goal.FStar_Tactics_Types.context  in
           let uu____3258 = __tc env t  in
           bind uu____3258
             (fun uu____3277  ->
                match uu____3277 with
                | (t1,typ,guard) ->
                    mlog
                      (fun uu____3292  ->
                         let uu____3293 =
                           tts goal.FStar_Tactics_Types.context typ  in
                         let uu____3294 =
                           FStar_TypeChecker_Rel.guard_to_string
                             goal.FStar_Tactics_Types.context guard
                            in
                         FStar_Util.print2
                           "__exact_now: got type %s\n__exact_now: and guard %s\n"
                           uu____3293 uu____3294)
                      (fun uu____3297  ->
                         let uu____3298 =
                           proc_guard "__exact typing"
                             goal.FStar_Tactics_Types.context guard
                             goal.FStar_Tactics_Types.opts
                            in
                         bind uu____3298
                           (fun uu____3302  ->
                              mlog
                                (fun uu____3306  ->
                                   let uu____3307 =
                                     tts goal.FStar_Tactics_Types.context typ
                                      in
                                   let uu____3308 =
                                     tts goal.FStar_Tactics_Types.context
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   FStar_Util.print2
                                     "__exact_now: unifying %s and %s\n"
                                     uu____3307 uu____3308)
                                (fun uu____3311  ->
                                   let uu____3312 =
                                     do_unify
                                       goal.FStar_Tactics_Types.context typ
                                       goal.FStar_Tactics_Types.goal_ty
                                      in
                                   bind uu____3312
                                     (fun b  ->
                                        if b
                                        then solve goal t1
                                        else
                                          (let uu____3320 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               t1
                                              in
                                           let uu____3321 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               typ
                                              in
                                           let uu____3322 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.goal_ty
                                              in
                                           let uu____3323 =
                                             tts
                                               goal.FStar_Tactics_Types.context
                                               goal.FStar_Tactics_Types.witness
                                              in
                                           fail4
                                             "%s : %s does not exactly solve the goal %s (witness = %s)"
                                             uu____3320 uu____3321 uu____3322
                                             uu____3323)))))))
  
let (t_exact : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun set_expected_typ1  ->
    fun tm  ->
      let uu____3338 =
        mlog
          (fun uu____3343  ->
             let uu____3344 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "t_exact: tm = %s\n" uu____3344)
          (fun uu____3347  ->
             let uu____3348 =
               let uu____3355 = __exact_now set_expected_typ1 tm  in
               trytac' uu____3355  in
             bind uu____3348
               (fun uu___84_3364  ->
                  match uu___84_3364 with
                  | FStar_Util.Inr r -> ret ()
                  | FStar_Util.Inl e ->
                      mlog
                        (fun uu____3374  ->
                           FStar_Util.print_string
                             "__exact_now failed, trying refine...\n")
                        (fun uu____3377  ->
                           let uu____3378 =
                             let uu____3385 =
                               let uu____3388 =
                                 norm [FStar_Syntax_Embeddings.Delta]  in
                               bind uu____3388
                                 (fun uu____3393  ->
                                    let uu____3394 = refine_intro ()  in
                                    bind uu____3394
                                      (fun uu____3398  ->
                                         __exact_now set_expected_typ1 tm))
                                in
                             trytac' uu____3385  in
                           bind uu____3378
                             (fun uu___83_3405  ->
                                match uu___83_3405 with
                                | FStar_Util.Inr r -> ret ()
                                | FStar_Util.Inl uu____3413 -> fail e))))
         in
      FStar_All.pipe_left (wrap_err "exact") uu____3338
  
let (uvar_free_in_goal :
  FStar_Syntax_Syntax.uvar -> FStar_Tactics_Types.goal -> Prims.bool) =
  fun u  ->
    fun g  ->
      if g.FStar_Tactics_Types.is_guard
      then false
      else
        (let free_uvars =
           let uu____3432 =
             let uu____3439 =
               FStar_Syntax_Free.uvars g.FStar_Tactics_Types.goal_ty  in
             FStar_Util.set_elements uu____3439  in
           FStar_List.map FStar_Pervasives_Native.fst uu____3432  in
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
          let uu____3509 = f x  in
          bind uu____3509
            (fun y  ->
               let uu____3517 = mapM f xs  in
               bind uu____3517 (fun ys  -> ret (y :: ys)))
  
exception NoUnif 
let (uu___is_NoUnif : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoUnif  -> true | uu____3537 -> false
  
let rec (__apply :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Reflection_Data.typ -> unit tac)
  =
  fun uopt  ->
    fun tm  ->
      fun typ  ->
        let uu____3557 = cur_goal ()  in
        bind uu____3557
          (fun goal  ->
             mlog
               (fun uu____3564  ->
                  let uu____3565 = FStar_Syntax_Print.term_to_string tm  in
                  FStar_Util.print1 ">>> Calling __exact(%s)\n" uu____3565)
               (fun uu____3568  ->
                  let uu____3569 =
                    let uu____3574 =
                      let uu____3577 = t_exact false tm  in
                      with_policy FStar_Tactics_Types.Force uu____3577  in
                    trytac_exn uu____3574  in
                  bind uu____3569
                    (fun uu___85_3584  ->
                       match uu___85_3584 with
                       | FStar_Pervasives_Native.Some r -> ret ()
                       | FStar_Pervasives_Native.None  ->
                           mlog
                             (fun uu____3592  ->
                                let uu____3593 =
                                  FStar_Syntax_Print.term_to_string typ  in
                                FStar_Util.print1 ">>> typ = %s\n" uu____3593)
                             (fun uu____3596  ->
                                let uu____3597 =
                                  FStar_Syntax_Util.arrow_one typ  in
                                match uu____3597 with
                                | FStar_Pervasives_Native.None  ->
                                    FStar_Exn.raise NoUnif
                                | FStar_Pervasives_Native.Some ((bv,aq),c) ->
                                    mlog
                                      (fun uu____3629  ->
                                         let uu____3630 =
                                           FStar_Syntax_Print.binder_to_string
                                             (bv, aq)
                                            in
                                         FStar_Util.print1
                                           "__apply: pushing binder %s\n"
                                           uu____3630)
                                      (fun uu____3633  ->
                                         let uu____3634 =
                                           let uu____3635 =
                                             FStar_Syntax_Util.is_total_comp
                                               c
                                              in
                                           Prims.op_Negation uu____3635  in
                                         if uu____3634
                                         then
                                           fail "apply: not total codomain"
                                         else
                                           (let uu____3639 =
                                              new_uvar "apply"
                                                goal.FStar_Tactics_Types.context
                                                bv.FStar_Syntax_Syntax.sort
                                               in
                                            bind uu____3639
                                              (fun u  ->
                                                 let tm' =
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     tm [(u, aq)]
                                                     FStar_Pervasives_Native.None
                                                     tm.FStar_Syntax_Syntax.pos
                                                    in
                                                 let typ' =
                                                   let uu____3659 =
                                                     comp_to_typ c  in
                                                   FStar_All.pipe_left
                                                     (FStar_Syntax_Subst.subst
                                                        [FStar_Syntax_Syntax.NT
                                                           (bv, u)])
                                                     uu____3659
                                                    in
                                                 let uu____3660 =
                                                   __apply uopt tm' typ'  in
                                                 bind uu____3660
                                                   (fun uu____3668  ->
                                                      let u1 =
                                                        bnorm
                                                          goal.FStar_Tactics_Types.context
                                                          u
                                                         in
                                                      let uu____3670 =
                                                        let uu____3671 =
                                                          let uu____3674 =
                                                            let uu____3675 =
                                                              FStar_Syntax_Util.head_and_args
                                                                u1
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____3675
                                                             in
                                                          FStar_Syntax_Subst.compress
                                                            uu____3674
                                                           in
                                                        uu____3671.FStar_Syntax_Syntax.n
                                                         in
                                                      match uu____3670 with
                                                      | FStar_Syntax_Syntax.Tm_uvar
                                                          (uvar,uu____3703)
                                                          ->
                                                          bind get
                                                            (fun ps  ->
                                                               let uu____3731
                                                                 =
                                                                 uopt &&
                                                                   (uvar_free
                                                                    uvar ps)
                                                                  in
                                                               if uu____3731
                                                               then ret ()
                                                               else
                                                                 (let uu____3735
                                                                    =
                                                                    let uu____3738
                                                                    =
                                                                    let uu___119_3739
                                                                    = goal
                                                                     in
                                                                    let uu____3740
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    u1  in
                                                                    let uu____3741
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___119_3739.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____3740;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____3741;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___119_3739.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    = false
                                                                    }  in
                                                                    [uu____3738]
                                                                     in
                                                                  add_goals
                                                                    uu____3735))
                                                      | t -> ret ()))))))))
  
let try_unif : 'a . 'a tac -> 'a tac -> 'a tac =
  fun t  ->
    fun t'  -> mk_tac (fun ps  -> try run t ps with | NoUnif  -> run t' ps)
  
let (apply : Prims.bool -> FStar_Syntax_Syntax.term -> unit tac) =
  fun uopt  ->
    fun tm  ->
      let uu____3796 =
        mlog
          (fun uu____3801  ->
             let uu____3802 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply: tm = %s\n" uu____3802)
          (fun uu____3805  ->
             let uu____3806 = cur_goal ()  in
             bind uu____3806
               (fun goal  ->
                  let uu____3812 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____3812
                    (fun uu____3834  ->
                       match uu____3834 with
                       | (tm1,typ,guard) ->
                           let typ1 =
                             bnorm goal.FStar_Tactics_Types.context typ  in
                           let uu____3847 =
                             let uu____3850 =
                               let uu____3853 = __apply uopt tm1 typ1  in
                               bind uu____3853
                                 (fun uu____3857  ->
                                    proc_guard "apply guard"
                                      goal.FStar_Tactics_Types.context guard
                                      goal.FStar_Tactics_Types.opts)
                                in
                             focus uu____3850  in
                           let uu____3858 =
                             let uu____3861 =
                               tts goal.FStar_Tactics_Types.context tm1  in
                             let uu____3862 =
                               tts goal.FStar_Tactics_Types.context typ1  in
                             let uu____3863 =
                               tts goal.FStar_Tactics_Types.context
                                 goal.FStar_Tactics_Types.goal_ty
                                in
                             fail3
                               "Cannot instantiate %s (of type %s) to match goal (%s)"
                               uu____3861 uu____3862 uu____3863
                              in
                           try_unif uu____3847 uu____3858)))
         in
      FStar_All.pipe_left (wrap_err "apply") uu____3796
  
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun c  ->
    let ct = FStar_Syntax_Util.comp_to_comp_typ_nouniv c  in
    let uu____3886 =
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Parser_Const.effect_Lemma_lid
       in
    if uu____3886
    then
      let uu____3893 =
        match ct.FStar_Syntax_Syntax.effect_args with
        | pre::post::uu____3912 ->
            ((FStar_Pervasives_Native.fst pre),
              (FStar_Pervasives_Native.fst post))
        | uu____3953 -> failwith "apply_lemma: impossible: not a lemma"  in
      match uu____3893 with
      | (pre,post) ->
          let post1 =
            let uu____3989 =
              let uu____3998 =
                FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit  in
              [uu____3998]  in
            FStar_Syntax_Util.mk_app post uu____3989  in
          FStar_Pervasives_Native.Some (pre, post1)
    else
      (let uu____4012 =
         FStar_Syntax_Util.is_pure_effect ct.FStar_Syntax_Syntax.effect_name
          in
       if uu____4012
       then
         let uu____4019 =
           FStar_Syntax_Util.un_squash ct.FStar_Syntax_Syntax.result_typ  in
         FStar_Util.map_opt uu____4019
           (fun post  -> (FStar_Syntax_Util.t_true, post))
       else FStar_Pervasives_Native.None)
  
let (apply_lemma : FStar_Syntax_Syntax.term -> unit tac) =
  fun tm  ->
    let uu____4052 =
      let uu____4055 =
        mlog
          (fun uu____4060  ->
             let uu____4061 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "apply_lemma: tm = %s\n" uu____4061)
          (fun uu____4065  ->
             let is_unit_t t =
               let uu____4072 =
                 let uu____4073 = FStar_Syntax_Subst.compress t  in
                 uu____4073.FStar_Syntax_Syntax.n  in
               match uu____4072 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.unit_lid
                   -> true
               | uu____4077 -> false  in
             let uu____4078 = cur_goal ()  in
             bind uu____4078
               (fun goal  ->
                  let uu____4084 = __tc goal.FStar_Tactics_Types.context tm
                     in
                  bind uu____4084
                    (fun uu____4107  ->
                       match uu____4107 with
                       | (tm1,t,guard) ->
                           let uu____4119 =
                             FStar_Syntax_Util.arrow_formals_comp t  in
                           (match uu____4119 with
                            | (bs,comp) ->
                                let uu____4146 = lemma_or_sq comp  in
                                (match uu____4146 with
                                 | FStar_Pervasives_Native.None  ->
                                     fail "not a lemma or squashed function"
                                 | FStar_Pervasives_Native.Some (pre,post) ->
                                     let uu____4165 =
                                       FStar_List.fold_left
                                         (fun uu____4207  ->
                                            fun uu____4208  ->
                                              match (uu____4207, uu____4208)
                                              with
                                              | ((uvs,guard1,subst1),(b,aq))
                                                  ->
                                                  let b_t =
                                                    FStar_Syntax_Subst.subst
                                                      subst1
                                                      b.FStar_Syntax_Syntax.sort
                                                     in
                                                  let uu____4299 =
                                                    is_unit_t b_t  in
                                                  if uu____4299
                                                  then
                                                    (((FStar_Syntax_Util.exp_unit,
                                                        aq) :: uvs), guard1,
                                                      ((FStar_Syntax_Syntax.NT
                                                          (b,
                                                            FStar_Syntax_Util.exp_unit))
                                                      :: subst1))
                                                  else
                                                    (let uu____4327 =
                                                       FStar_TypeChecker_Util.new_implicit_var
                                                         "apply_lemma"
                                                         (goal.FStar_Tactics_Types.goal_ty).FStar_Syntax_Syntax.pos
                                                         goal.FStar_Tactics_Types.context
                                                         b_t
                                                        in
                                                     match uu____4327 with
                                                     | (u,uu____4355,g_u) ->
                                                         let uu____4369 =
                                                           FStar_TypeChecker_Rel.conj_guard
                                                             guard1 g_u
                                                            in
                                                         (((u, aq) :: uvs),
                                                           uu____4369,
                                                           ((FStar_Syntax_Syntax.NT
                                                               (b, u)) ::
                                                           subst1))))
                                         ([], guard, []) bs
                                        in
                                     (match uu____4165 with
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
                                          let uu____4428 =
                                            let uu____4431 =
                                              FStar_Syntax_Util.mk_squash
                                                FStar_Syntax_Syntax.U_zero
                                                post1
                                               in
                                            do_unify
                                              goal.FStar_Tactics_Types.context
                                              uu____4431
                                              goal.FStar_Tactics_Types.goal_ty
                                             in
                                          bind uu____4428
                                            (fun b  ->
                                               if Prims.op_Negation b
                                               then
                                                 let uu____4439 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     tm1
                                                    in
                                                 let uu____4440 =
                                                   let uu____4441 =
                                                     FStar_Syntax_Util.mk_squash
                                                       FStar_Syntax_Syntax.U_zero
                                                       post1
                                                      in
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     uu____4441
                                                    in
                                                 let uu____4442 =
                                                   tts
                                                     goal.FStar_Tactics_Types.context
                                                     goal.FStar_Tactics_Types.goal_ty
                                                    in
                                                 fail3
                                                   "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                   uu____4439 uu____4440
                                                   uu____4442
                                               else
                                                 (let uu____4444 =
                                                    add_implicits
                                                      implicits.FStar_TypeChecker_Env.implicits
                                                     in
                                                  bind uu____4444
                                                    (fun uu____4449  ->
                                                       let uu____4450 =
                                                         solve goal
                                                           FStar_Syntax_Util.exp_unit
                                                          in
                                                       bind uu____4450
                                                         (fun uu____4458  ->
                                                            let is_free_uvar
                                                              uv t1 =
                                                              let free_uvars
                                                                =
                                                                let uu____4473
                                                                  =
                                                                  let uu____4480
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1  in
                                                                  FStar_Util.set_elements
                                                                    uu____4480
                                                                   in
                                                                FStar_List.map
                                                                  FStar_Pervasives_Native.fst
                                                                  uu____4473
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
                                                              let uu____4529
                                                                =
                                                                FStar_Syntax_Util.head_and_args
                                                                  t1
                                                                 in
                                                              match uu____4529
                                                              with
                                                              | (hd1,uu____4545)
                                                                  ->
                                                                  (match 
                                                                    hd1.FStar_Syntax_Syntax.n
                                                                   with
                                                                   | 
                                                                   FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,uu____4567)
                                                                    ->
                                                                    appears
                                                                    uv goals
                                                                   | 
                                                                   uu____4592
                                                                    -> false)
                                                               in
                                                            let uu____4593 =
                                                              FStar_All.pipe_right
                                                                implicits.FStar_TypeChecker_Env.implicits
                                                                (mapM
                                                                   (fun
                                                                    uu____4665
                                                                     ->
                                                                    match uu____4665
                                                                    with
                                                                    | 
                                                                    (_msg,env,_uvar,term,typ,uu____4693)
                                                                    ->
                                                                    let uu____4694
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    term  in
                                                                    (match uu____4694
                                                                    with
                                                                    | 
                                                                    (hd1,uu____4720)
                                                                    ->
                                                                    let uu____4741
                                                                    =
                                                                    let uu____4742
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    hd1  in
                                                                    uu____4742.FStar_Syntax_Syntax.n
                                                                     in
                                                                    (match uu____4741
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    uu____4755
                                                                    ->
                                                                    let uu____4772
                                                                    =
                                                                    let uu____4781
                                                                    =
                                                                    let uu____4784
                                                                    =
                                                                    let uu___122_4785
                                                                    = goal
                                                                     in
                                                                    let uu____4786
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    term  in
                                                                    let uu____4787
                                                                    =
                                                                    bnorm
                                                                    goal.FStar_Tactics_Types.context
                                                                    typ  in
                                                                    {
                                                                    FStar_Tactics_Types.context
                                                                    =
                                                                    (uu___122_4785.FStar_Tactics_Types.context);
                                                                    FStar_Tactics_Types.witness
                                                                    =
                                                                    uu____4786;
                                                                    FStar_Tactics_Types.goal_ty
                                                                    =
                                                                    uu____4787;
                                                                    FStar_Tactics_Types.opts
                                                                    =
                                                                    (uu___122_4785.FStar_Tactics_Types.opts);
                                                                    FStar_Tactics_Types.is_guard
                                                                    =
                                                                    (uu___122_4785.FStar_Tactics_Types.is_guard)
                                                                    }  in
                                                                    [uu____4784]
                                                                     in
                                                                    (uu____4781,
                                                                    [])  in
                                                                    ret
                                                                    uu____4772
                                                                    | 
                                                                    uu____4800
                                                                    ->
                                                                    let g_typ
                                                                    =
                                                                    let uu____4802
                                                                    =
                                                                    FStar_Options.__temp_fast_implicits
                                                                    ()  in
                                                                    if
                                                                    uu____4802
                                                                    then
                                                                    FStar_TypeChecker_TcTerm.check_type_of_well_typed_term
                                                                    false env
                                                                    term typ
                                                                    else
                                                                    (let term1
                                                                    =
                                                                    bnorm env
                                                                    term  in
                                                                    let uu____4805
                                                                    =
                                                                    let uu____4812
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env typ
                                                                     in
                                                                    env.FStar_TypeChecker_Env.type_of
                                                                    uu____4812
                                                                    term1  in
                                                                    match uu____4805
                                                                    with
                                                                    | 
                                                                    (uu____4813,uu____4814,g_typ)
                                                                    -> g_typ)
                                                                     in
                                                                    let uu____4816
                                                                    =
                                                                    goal_from_guard
                                                                    "apply_lemma solved arg"
                                                                    goal.FStar_Tactics_Types.context
                                                                    g_typ
                                                                    goal.FStar_Tactics_Types.opts
                                                                     in
                                                                    bind
                                                                    uu____4816
                                                                    (fun
                                                                    uu___86_4832
                                                                     ->
                                                                    match uu___86_4832
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
                                                            bind uu____4593
                                                              (fun goals_  ->
                                                                 let sub_goals
                                                                   =
                                                                   let uu____4900
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.fst
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4900
                                                                    in
                                                                 let smt_goals
                                                                   =
                                                                   let uu____4922
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_Pervasives_Native.snd
                                                                    goals_
                                                                     in
                                                                   FStar_List.flatten
                                                                    uu____4922
                                                                    in
                                                                 let rec filter'
                                                                   f xs =
                                                                   match xs
                                                                   with
                                                                   | 
                                                                   [] -> []
                                                                   | 
                                                                   x::xs1 ->
                                                                    let uu____4983
                                                                    = f x xs1
                                                                     in
                                                                    if
                                                                    uu____4983
                                                                    then
                                                                    let uu____4986
                                                                    =
                                                                    filter' f
                                                                    xs1  in x
                                                                    ::
                                                                    uu____4986
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
                                                                    let uu____5000
                                                                    =
                                                                    checkone
                                                                    g.FStar_Tactics_Types.witness
                                                                    goals  in
                                                                    Prims.op_Negation
                                                                    uu____5000)
                                                                    sub_goals
                                                                    in
                                                                 let uu____5001
                                                                   =
                                                                   proc_guard
                                                                    "apply_lemma guard"
                                                                    goal.FStar_Tactics_Types.context
                                                                    guard
                                                                    goal.FStar_Tactics_Types.opts
                                                                    in
                                                                 bind
                                                                   uu____5001
                                                                   (fun
                                                                    uu____5006
                                                                     ->
                                                                    let uu____5007
                                                                    =
                                                                    let uu____5010
                                                                    =
                                                                    let uu____5011
                                                                    =
                                                                    let uu____5012
                                                                    =
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    pre1  in
                                                                    istrivial
                                                                    goal.FStar_Tactics_Types.context
                                                                    uu____5012
                                                                     in
                                                                    Prims.op_Negation
                                                                    uu____5011
                                                                     in
                                                                    if
                                                                    uu____5010
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
                                                                    uu____5007
                                                                    (fun
                                                                    uu____5018
                                                                     ->
                                                                    let uu____5019
                                                                    =
                                                                    add_smt_goals
                                                                    smt_goals
                                                                     in
                                                                    bind
                                                                    uu____5019
                                                                    (fun
                                                                    uu____5023
                                                                     ->
                                                                    add_goals
                                                                    sub_goals1))))))))))))))
         in
      focus uu____4055  in
    FStar_All.pipe_left (wrap_err "apply_lemma") uu____4052
  
let (destruct_eq' :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5045 = FStar_Syntax_Util.destruct_typ_as_formula typ  in
    match uu____5045 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,uu____5055::(e1,uu____5057)::(e2,uu____5059)::[])) when
        FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid ->
        FStar_Pervasives_Native.Some (e1, e2)
    | uu____5118 -> FStar_Pervasives_Native.None
  
let (destruct_eq :
  FStar_Reflection_Data.typ ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun typ  ->
    let uu____5142 = destruct_eq' typ  in
    match uu____5142 with
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
    | FStar_Pervasives_Native.None  ->
        let uu____5172 = FStar_Syntax_Util.un_squash typ  in
        (match uu____5172 with
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
        let uu____5234 = FStar_TypeChecker_Env.pop_bv e1  in
        match uu____5234 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv',e') ->
            if FStar_Syntax_Syntax.bv_eq bvar bv'
            then FStar_Pervasives_Native.Some (e', [])
            else
              (let uu____5282 = aux e'  in
               FStar_Util.map_opt uu____5282
                 (fun uu____5306  ->
                    match uu____5306 with | (e'',bvs) -> (e'', (bv' :: bvs))))
         in
      let uu____5327 = aux e  in
      FStar_Util.map_opt uu____5327
        (fun uu____5351  ->
           match uu____5351 with | (e',bvs) -> (e', (FStar_List.rev bvs)))
  
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
          let uu____5418 = split_env b1 g.FStar_Tactics_Types.context  in
          FStar_Util.map_opt uu____5418
            (fun uu____5442  ->
               match uu____5442 with
               | (e0,bvs) ->
                   let s1 bv =
                     let uu___123_5461 = bv  in
                     let uu____5462 =
                       FStar_Syntax_Subst.subst s bv.FStar_Syntax_Syntax.sort
                        in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___123_5461.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___123_5461.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = uu____5462
                     }  in
                   let bvs1 = FStar_List.map s1 bvs  in
                   let c = push_bvs e0 (b2 :: bvs1)  in
                   let w =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.witness
                      in
                   let t =
                     FStar_Syntax_Subst.subst s g.FStar_Tactics_Types.goal_ty
                      in
                   let uu___124_5471 = g  in
                   {
                     FStar_Tactics_Types.context = c;
                     FStar_Tactics_Types.witness = w;
                     FStar_Tactics_Types.goal_ty = t;
                     FStar_Tactics_Types.opts =
                       (uu___124_5471.FStar_Tactics_Types.opts);
                     FStar_Tactics_Types.is_guard =
                       (uu___124_5471.FStar_Tactics_Types.is_guard)
                   })
  
let (rewrite : FStar_Syntax_Syntax.binder -> unit tac) =
  fun h  ->
    let uu____5481 = cur_goal ()  in
    bind uu____5481
      (fun goal  ->
         let uu____5489 = h  in
         match uu____5489 with
         | (bv,uu____5493) ->
             mlog
               (fun uu____5497  ->
                  let uu____5498 = FStar_Syntax_Print.bv_to_string bv  in
                  let uu____5499 =
                    tts goal.FStar_Tactics_Types.context
                      bv.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2 "+++Rewrite %s : %s\n" uu____5498
                    uu____5499)
               (fun uu____5502  ->
                  let uu____5503 =
                    split_env bv goal.FStar_Tactics_Types.context  in
                  match uu____5503 with
                  | FStar_Pervasives_Native.None  ->
                      fail "rewrite: binder not found in environment"
                  | FStar_Pervasives_Native.Some (e0,bvs) ->
                      let uu____5532 =
                        destruct_eq bv.FStar_Syntax_Syntax.sort  in
                      (match uu____5532 with
                       | FStar_Pervasives_Native.Some (x,e) ->
                           let uu____5547 =
                             let uu____5548 = FStar_Syntax_Subst.compress x
                                in
                             uu____5548.FStar_Syntax_Syntax.n  in
                           (match uu____5547 with
                            | FStar_Syntax_Syntax.Tm_name x1 ->
                                let s = [FStar_Syntax_Syntax.NT (x1, e)]  in
                                let s1 bv1 =
                                  let uu___125_5563 = bv1  in
                                  let uu____5564 =
                                    FStar_Syntax_Subst.subst s
                                      bv1.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___125_5563.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___125_5563.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____5564
                                  }  in
                                let bvs1 = FStar_List.map s1 bvs  in
                                let uu____5570 =
                                  let uu___126_5571 = goal  in
                                  let uu____5572 = push_bvs e0 (bv :: bvs1)
                                     in
                                  let uu____5573 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.witness
                                     in
                                  let uu____5574 =
                                    FStar_Syntax_Subst.subst s
                                      goal.FStar_Tactics_Types.goal_ty
                                     in
                                  {
                                    FStar_Tactics_Types.context = uu____5572;
                                    FStar_Tactics_Types.witness = uu____5573;
                                    FStar_Tactics_Types.goal_ty = uu____5574;
                                    FStar_Tactics_Types.opts =
                                      (uu___126_5571.FStar_Tactics_Types.opts);
                                    FStar_Tactics_Types.is_guard =
                                      (uu___126_5571.FStar_Tactics_Types.is_guard)
                                  }  in
                                replace_cur uu____5570
                            | uu____5575 ->
                                fail
                                  "rewrite: Not an equality hypothesis with a variable on the LHS")
                       | uu____5576 ->
                           fail "rewrite: Not an equality hypothesis")))
  
let (rename_to : FStar_Syntax_Syntax.binder -> Prims.string -> unit tac) =
  fun b  ->
    fun s  ->
      let uu____5597 = cur_goal ()  in
      bind uu____5597
        (fun goal  ->
           let uu____5608 = b  in
           match uu____5608 with
           | (bv,uu____5612) ->
               let bv' =
                 let uu____5614 =
                   let uu___127_5615 = bv  in
                   let uu____5616 =
                     FStar_Ident.mk_ident
                       (s,
                         ((bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
                      in
                   {
                     FStar_Syntax_Syntax.ppname = uu____5616;
                     FStar_Syntax_Syntax.index =
                       (uu___127_5615.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (uu___127_5615.FStar_Syntax_Syntax.sort)
                   }  in
                 FStar_Syntax_Syntax.freshen_bv uu____5614  in
               let s1 =
                 let uu____5620 =
                   let uu____5621 =
                     let uu____5628 = FStar_Syntax_Syntax.bv_to_name bv'  in
                     (bv, uu____5628)  in
                   FStar_Syntax_Syntax.NT uu____5621  in
                 [uu____5620]  in
               let uu____5629 = subst_goal bv bv' s1 goal  in
               (match uu____5629 with
                | FStar_Pervasives_Native.None  ->
                    fail "rename_to: binder not found in environment"
                | FStar_Pervasives_Native.Some goal1 -> replace_cur goal1))
  
let (binder_retype : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let uu____5644 = cur_goal ()  in
    bind uu____5644
      (fun goal  ->
         let uu____5653 = b  in
         match uu____5653 with
         | (bv,uu____5657) ->
             let uu____5658 = split_env bv goal.FStar_Tactics_Types.context
                in
             (match uu____5658 with
              | FStar_Pervasives_Native.None  ->
                  fail "binder_retype: binder is not present in environment"
              | FStar_Pervasives_Native.Some (e0,bvs) ->
                  let uu____5687 = FStar_Syntax_Util.type_u ()  in
                  (match uu____5687 with
                   | (ty,u) ->
                       let uu____5696 = new_uvar "binder_retype" e0 ty  in
                       bind uu____5696
                         (fun t'  ->
                            let bv'' =
                              let uu___128_5706 = bv  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___128_5706.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___128_5706.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t'
                              }  in
                            let s =
                              let uu____5710 =
                                let uu____5711 =
                                  let uu____5718 =
                                    FStar_Syntax_Syntax.bv_to_name bv''  in
                                  (bv, uu____5718)  in
                                FStar_Syntax_Syntax.NT uu____5711  in
                              [uu____5710]  in
                            let bvs1 =
                              FStar_List.map
                                (fun b1  ->
                                   let uu___129_5726 = b1  in
                                   let uu____5727 =
                                     FStar_Syntax_Subst.subst s
                                       b1.FStar_Syntax_Syntax.sort
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___129_5726.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___129_5726.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____5727
                                   }) bvs
                               in
                            let env' = push_bvs e0 (bv'' :: bvs1)  in
                            bind __dismiss
                              (fun uu____5733  ->
                                 let uu____5734 =
                                   let uu____5737 =
                                     let uu____5740 =
                                       let uu___130_5741 = goal  in
                                       let uu____5742 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.witness
                                          in
                                       let uu____5743 =
                                         FStar_Syntax_Subst.subst s
                                           goal.FStar_Tactics_Types.goal_ty
                                          in
                                       {
                                         FStar_Tactics_Types.context = env';
                                         FStar_Tactics_Types.witness =
                                           uu____5742;
                                         FStar_Tactics_Types.goal_ty =
                                           uu____5743;
                                         FStar_Tactics_Types.opts =
                                           (uu___130_5741.FStar_Tactics_Types.opts);
                                         FStar_Tactics_Types.is_guard =
                                           (uu___130_5741.FStar_Tactics_Types.is_guard)
                                       }  in
                                     [uu____5740]  in
                                   add_goals uu____5737  in
                                 bind uu____5734
                                   (fun uu____5746  ->
                                      let uu____5747 =
                                        FStar_Syntax_Util.mk_eq2
                                          (FStar_Syntax_Syntax.U_succ u) ty
                                          bv.FStar_Syntax_Syntax.sort t'
                                         in
                                      add_irrelevant_goal
                                        "binder_retype equation" e0
                                        uu____5747
                                        goal.FStar_Tactics_Types.opts))))))
  
let (norm_binder_type :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit tac)
  =
  fun s  ->
    fun b  ->
      let uu____5766 = cur_goal ()  in
      bind uu____5766
        (fun goal  ->
           let uu____5775 = b  in
           match uu____5775 with
           | (bv,uu____5779) ->
               let uu____5780 = split_env bv goal.FStar_Tactics_Types.context
                  in
               (match uu____5780 with
                | FStar_Pervasives_Native.None  ->
                    fail
                      "binder_retype: binder is not present in environment"
                | FStar_Pervasives_Native.Some (e0,bvs) ->
                    let steps =
                      let uu____5812 =
                        FStar_TypeChecker_Normalize.tr_norm_steps s  in
                      FStar_List.append
                        [FStar_TypeChecker_Normalize.Reify;
                        FStar_TypeChecker_Normalize.UnfoldTac] uu____5812
                       in
                    let sort' =
                      normalize steps e0 bv.FStar_Syntax_Syntax.sort  in
                    let bv' =
                      let uu___131_5817 = bv  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___131_5817.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___131_5817.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort'
                      }  in
                    let env' = push_bvs e0 (bv' :: bvs)  in
                    replace_cur
                      (let uu___132_5821 = goal  in
                       {
                         FStar_Tactics_Types.context = env';
                         FStar_Tactics_Types.witness =
                           (uu___132_5821.FStar_Tactics_Types.witness);
                         FStar_Tactics_Types.goal_ty =
                           (uu___132_5821.FStar_Tactics_Types.goal_ty);
                         FStar_Tactics_Types.opts =
                           (uu___132_5821.FStar_Tactics_Types.opts);
                         FStar_Tactics_Types.is_guard =
                           (uu___132_5821.FStar_Tactics_Types.is_guard)
                       })))
  
let (revert : unit -> unit tac) =
  fun uu____5828  ->
    let uu____5831 = cur_goal ()  in
    bind uu____5831
      (fun goal  ->
         let uu____5837 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____5837 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x,env') ->
             let typ' =
               let uu____5859 =
                 FStar_Syntax_Syntax.mk_Total
                   goal.FStar_Tactics_Types.goal_ty
                  in
               FStar_Syntax_Util.arrow [(x, FStar_Pervasives_Native.None)]
                 uu____5859
                in
             let w' =
               FStar_Syntax_Util.abs [(x, FStar_Pervasives_Native.None)]
                 goal.FStar_Tactics_Types.witness
                 FStar_Pervasives_Native.None
                in
             replace_cur
               (let uu___133_5893 = goal  in
                {
                  FStar_Tactics_Types.context = env';
                  FStar_Tactics_Types.witness = w';
                  FStar_Tactics_Types.goal_ty = typ';
                  FStar_Tactics_Types.opts =
                    (uu___133_5893.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___133_5893.FStar_Tactics_Types.is_guard)
                }))
  
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____5904 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____5904
  
let rec (clear : FStar_Syntax_Syntax.binder -> unit tac) =
  fun b  ->
    let bv = FStar_Pervasives_Native.fst b  in
    let uu____5917 = cur_goal ()  in
    bind uu____5917
      (fun goal  ->
         mlog
           (fun uu____5925  ->
              let uu____5926 = FStar_Syntax_Print.binder_to_string b  in
              let uu____5927 =
                let uu____5928 =
                  let uu____5929 =
                    FStar_TypeChecker_Env.all_binders
                      goal.FStar_Tactics_Types.context
                     in
                  FStar_All.pipe_right uu____5929 FStar_List.length  in
                FStar_All.pipe_right uu____5928 FStar_Util.string_of_int  in
              FStar_Util.print2 "Clear of (%s), env has %s binders\n"
                uu____5926 uu____5927)
           (fun uu____5940  ->
              let uu____5941 = split_env bv goal.FStar_Tactics_Types.context
                 in
              match uu____5941 with
              | FStar_Pervasives_Native.None  ->
                  fail "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e',bvs) ->
                  let rec check1 bvs1 =
                    match bvs1 with
                    | [] -> ret ()
                    | bv'::bvs2 ->
                        let uu____5988 =
                          free_in bv bv'.FStar_Syntax_Syntax.sort  in
                        if uu____5988
                        then
                          let uu____5991 =
                            let uu____5992 =
                              FStar_Syntax_Print.bv_to_string bv'  in
                            FStar_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu____5992
                             in
                          fail uu____5991
                        else check1 bvs2
                     in
                  let uu____5994 =
                    free_in bv goal.FStar_Tactics_Types.goal_ty  in
                  if uu____5994
                  then fail "Cannot clear; binder present in goal"
                  else
                    (let uu____5998 = check1 bvs  in
                     bind uu____5998
                       (fun uu____6004  ->
                          let env' = push_bvs e' bvs  in
                          let uu____6006 =
                            new_uvar "clear.witness" env'
                              goal.FStar_Tactics_Types.goal_ty
                             in
                          bind uu____6006
                            (fun ut  ->
                               let uu____6012 =
                                 do_unify goal.FStar_Tactics_Types.context
                                   goal.FStar_Tactics_Types.witness ut
                                  in
                               bind uu____6012
                                 (fun b1  ->
                                    if b1
                                    then
                                      replace_cur
                                        (let uu___134_6021 = goal  in
                                         {
                                           FStar_Tactics_Types.context = env';
                                           FStar_Tactics_Types.witness = ut;
                                           FStar_Tactics_Types.goal_ty =
                                             (uu___134_6021.FStar_Tactics_Types.goal_ty);
                                           FStar_Tactics_Types.opts =
                                             (uu___134_6021.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___134_6021.FStar_Tactics_Types.is_guard)
                                         })
                                    else
                                      fail
                                        "Cannot clear; binder appears in witness"))))))
  
let (clear_top : unit -> unit tac) =
  fun uu____6029  ->
    let uu____6032 = cur_goal ()  in
    bind uu____6032
      (fun goal  ->
         let uu____6038 =
           FStar_TypeChecker_Env.pop_bv goal.FStar_Tactics_Types.context  in
         match uu____6038 with
         | FStar_Pervasives_Native.None  ->
             fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x,uu____6052) ->
             let uu____6057 = FStar_Syntax_Syntax.mk_binder x  in
             clear uu____6057)
  
let (prune : Prims.string -> unit tac) =
  fun s  ->
    let uu____6067 = cur_goal ()  in
    bind uu____6067
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6077 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu____6077  in
         let g' =
           let uu___135_6079 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___135_6079.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___135_6079.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___135_6079.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___135_6079.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6081  -> add_goals [g']))
  
let (addns : Prims.string -> unit tac) =
  fun s  ->
    let uu____6091 = cur_goal ()  in
    bind uu____6091
      (fun g  ->
         let ctx = g.FStar_Tactics_Types.context  in
         let ctx' =
           let uu____6101 = FStar_Ident.path_of_text s  in
           FStar_TypeChecker_Env.add_proof_ns ctx uu____6101  in
         let g' =
           let uu___136_6103 = g  in
           {
             FStar_Tactics_Types.context = ctx';
             FStar_Tactics_Types.witness =
               (uu___136_6103.FStar_Tactics_Types.witness);
             FStar_Tactics_Types.goal_ty =
               (uu___136_6103.FStar_Tactics_Types.goal_ty);
             FStar_Tactics_Types.opts =
               (uu___136_6103.FStar_Tactics_Types.opts);
             FStar_Tactics_Types.is_guard =
               (uu___136_6103.FStar_Tactics_Types.is_guard)
           }  in
         bind __dismiss (fun uu____6105  -> add_goals [g']))
  
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
            let uu____6145 = FStar_Syntax_Subst.compress t  in
            uu____6145.FStar_Syntax_Syntax.n  in
          let uu____6148 =
            if d = FStar_Tactics_Types.TopDown
            then
              f env
                (let uu___140_6154 = t  in
                 {
                   FStar_Syntax_Syntax.n = tn;
                   FStar_Syntax_Syntax.pos =
                     (uu___140_6154.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___140_6154.FStar_Syntax_Syntax.vars)
                 })
            else ret t  in
          bind uu____6148
            (fun t1  ->
               let ff = tac_fold_env d f env  in
               let tn1 =
                 let uu____6170 =
                   let uu____6171 = FStar_Syntax_Subst.compress t1  in
                   uu____6171.FStar_Syntax_Syntax.n  in
                 match uu____6170 with
                 | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                     let uu____6198 = ff hd1  in
                     bind uu____6198
                       (fun hd2  ->
                          let fa uu____6220 =
                            match uu____6220 with
                            | (a,q) ->
                                let uu____6233 = ff a  in
                                bind uu____6233 (fun a1  -> ret (a1, q))
                             in
                          let uu____6246 = mapM fa args  in
                          bind uu____6246
                            (fun args1  ->
                               ret (FStar_Syntax_Syntax.Tm_app (hd2, args1))))
                 | FStar_Syntax_Syntax.Tm_abs (bs,t2,k) ->
                     let uu____6306 = FStar_Syntax_Subst.open_term bs t2  in
                     (match uu____6306 with
                      | (bs1,t') ->
                          let uu____6315 =
                            let uu____6318 =
                              FStar_TypeChecker_Env.push_binders env bs1  in
                            tac_fold_env d f uu____6318 t'  in
                          bind uu____6315
                            (fun t''  ->
                               let uu____6322 =
                                 let uu____6323 =
                                   let uu____6340 =
                                     FStar_Syntax_Subst.close_binders bs1  in
                                   let uu____6341 =
                                     FStar_Syntax_Subst.close bs1 t''  in
                                   (uu____6340, uu____6341, k)  in
                                 FStar_Syntax_Syntax.Tm_abs uu____6323  in
                               ret uu____6322))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> ret tn
                 | FStar_Syntax_Syntax.Tm_match (hd1,brs) ->
                     let uu____6400 = ff hd1  in
                     bind uu____6400
                       (fun hd2  ->
                          let ffb br =
                            let uu____6415 =
                              FStar_Syntax_Subst.open_branch br  in
                            match uu____6415 with
                            | (pat,w,e) ->
                                let bvs = FStar_Syntax_Syntax.pat_bvs pat  in
                                let ff1 =
                                  let uu____6447 =
                                    FStar_TypeChecker_Env.push_bvs env bvs
                                     in
                                  tac_fold_env d f uu____6447  in
                                let uu____6448 = ff1 e  in
                                bind uu____6448
                                  (fun e1  ->
                                     let br1 =
                                       FStar_Syntax_Subst.close_branch
                                         (pat, w, e1)
                                        in
                                     ret br1)
                             in
                          let uu____6461 = mapM ffb brs  in
                          bind uu____6461
                            (fun brs1  ->
                               ret (FStar_Syntax_Syntax.Tm_match (hd2, brs1))))
                 | FStar_Syntax_Syntax.Tm_let
                     ((false
                       ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl bv;
                          FStar_Syntax_Syntax.lbunivs = uu____6475;
                          FStar_Syntax_Syntax.lbtyp = uu____6476;
                          FStar_Syntax_Syntax.lbeff = uu____6477;
                          FStar_Syntax_Syntax.lbdef = def;
                          FStar_Syntax_Syntax.lbattrs = uu____6479;
                          FStar_Syntax_Syntax.lbpos = uu____6480;_}::[]),e)
                     ->
                     let lb =
                       let uu____6505 =
                         let uu____6506 = FStar_Syntax_Subst.compress t1  in
                         uu____6506.FStar_Syntax_Syntax.n  in
                       match uu____6505 with
                       | FStar_Syntax_Syntax.Tm_let
                           ((false ,lb::[]),uu____6510) -> lb
                       | uu____6523 -> failwith "impossible"  in
                     let fflb lb1 =
                       let uu____6532 = ff lb1.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6532
                         (fun def1  ->
                            ret
                              (let uu___137_6538 = lb1  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___137_6538.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___137_6538.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___137_6538.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___137_6538.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def1;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___137_6538.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___137_6538.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6539 = fflb lb  in
                     bind uu____6539
                       (fun lb1  ->
                          let uu____6549 =
                            let uu____6554 =
                              let uu____6555 =
                                FStar_Syntax_Syntax.mk_binder bv  in
                              [uu____6555]  in
                            FStar_Syntax_Subst.open_term uu____6554 e  in
                          match uu____6549 with
                          | (bs,e1) ->
                              let ff1 =
                                let uu____6567 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                tac_fold_env d f uu____6567  in
                              let uu____6568 = ff1 e1  in
                              bind uu____6568
                                (fun e2  ->
                                   let e3 = FStar_Syntax_Subst.close bs e2
                                      in
                                   ret
                                     (FStar_Syntax_Syntax.Tm_let
                                        ((false, [lb1]), e3))))
                 | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e) ->
                     let fflb lb =
                       let uu____6607 = ff lb.FStar_Syntax_Syntax.lbdef  in
                       bind uu____6607
                         (fun def  ->
                            ret
                              (let uu___138_6613 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (uu___138_6613.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___138_6613.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___138_6613.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___138_6613.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___138_6613.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___138_6613.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     let uu____6614 = FStar_Syntax_Subst.open_let_rec lbs e
                        in
                     (match uu____6614 with
                      | (lbs1,e1) ->
                          let uu____6629 = mapM fflb lbs1  in
                          bind uu____6629
                            (fun lbs2  ->
                               let uu____6641 = ff e1  in
                               bind uu____6641
                                 (fun e2  ->
                                    let uu____6649 =
                                      FStar_Syntax_Subst.close_let_rec lbs2
                                        e2
                                       in
                                    match uu____6649 with
                                    | (lbs3,e3) ->
                                        ret
                                          (FStar_Syntax_Syntax.Tm_let
                                             ((true, lbs3), e3)))))
                 | FStar_Syntax_Syntax.Tm_ascribed (t2,asc,eff) ->
                     let uu____6715 = ff t2  in
                     bind uu____6715
                       (fun t3  ->
                          ret
                            (FStar_Syntax_Syntax.Tm_ascribed (t3, asc, eff)))
                 | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
                     let uu____6744 = ff t2  in
                     bind uu____6744
                       (fun t3  -> ret (FStar_Syntax_Syntax.Tm_meta (t3, m)))
                 | uu____6749 -> ret tn  in
               bind tn1
                 (fun tn2  ->
                    let t' =
                      let uu___139_6756 = t1  in
                      {
                        FStar_Syntax_Syntax.n = tn2;
                        FStar_Syntax_Syntax.pos =
                          (uu___139_6756.FStar_Syntax_Syntax.pos);
                        FStar_Syntax_Syntax.vars =
                          (uu___139_6756.FStar_Syntax_Syntax.vars)
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
            let uu____6795 = FStar_TypeChecker_TcTerm.tc_term env t  in
            match uu____6795 with
            | (t1,lcomp,g) ->
                let uu____6807 =
                  (let uu____6810 =
                     FStar_Syntax_Util.is_pure_or_ghost_lcomp lcomp  in
                   Prims.op_Negation uu____6810) ||
                    (let uu____6812 = FStar_TypeChecker_Rel.is_trivial g  in
                     Prims.op_Negation uu____6812)
                   in
                if uu____6807
                then ret t1
                else
                  (let rewrite_eq =
                     let typ = lcomp.FStar_Syntax_Syntax.res_typ  in
                     let uu____6820 = new_uvar "pointwise_rec" env typ  in
                     bind uu____6820
                       (fun ut  ->
                          log ps
                            (fun uu____6831  ->
                               let uu____6832 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____6833 =
                                 FStar_Syntax_Print.term_to_string ut  in
                               FStar_Util.print2
                                 "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                 uu____6832 uu____6833);
                          (let uu____6834 =
                             let uu____6837 =
                               let uu____6838 =
                                 FStar_TypeChecker_TcTerm.universe_of env typ
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____6838 typ t1 ut
                                in
                             add_irrelevant_goal "pointwise_rec equation" env
                               uu____6837 opts
                              in
                           bind uu____6834
                             (fun uu____6841  ->
                                let uu____6842 =
                                  bind tau
                                    (fun uu____6848  ->
                                       let ut1 =
                                         FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                           env ut
                                          in
                                       log ps
                                         (fun uu____6854  ->
                                            let uu____6855 =
                                              FStar_Syntax_Print.term_to_string
                                                t1
                                               in
                                            let uu____6856 =
                                              FStar_Syntax_Print.term_to_string
                                                ut1
                                               in
                                            FStar_Util.print2
                                              "Pointwise_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                              uu____6855 uu____6856);
                                       ret ut1)
                                   in
                                focus uu____6842)))
                      in
                   let uu____6857 = trytac' rewrite_eq  in
                   bind uu____6857
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
          let uu____7029 = FStar_Syntax_Subst.compress t  in
          maybe_continue ctrl uu____7029
            (fun t1  ->
               let uu____7033 =
                 f env
                   (let uu___143_7042 = t1  in
                    {
                      FStar_Syntax_Syntax.n = (t1.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos =
                        (uu___143_7042.FStar_Syntax_Syntax.pos);
                      FStar_Syntax_Syntax.vars =
                        (uu___143_7042.FStar_Syntax_Syntax.vars)
                    })
                  in
               bind uu____7033
                 (fun uu____7054  ->
                    match uu____7054 with
                    | (t2,ctrl1) ->
                        maybe_continue ctrl1 t2
                          (fun t3  ->
                             let uu____7073 =
                               let uu____7074 =
                                 FStar_Syntax_Subst.compress t3  in
                               uu____7074.FStar_Syntax_Syntax.n  in
                             match uu____7073 with
                             | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
                                 let uu____7107 =
                                   ctrl_tac_fold f env ctrl1 hd1  in
                                 bind uu____7107
                                   (fun uu____7132  ->
                                      match uu____7132 with
                                      | (hd2,ctrl2) ->
                                          let ctrl3 = keep_going ctrl2  in
                                          let uu____7148 =
                                            ctrl_tac_fold_args f env ctrl3
                                              args
                                             in
                                          bind uu____7148
                                            (fun uu____7175  ->
                                               match uu____7175 with
                                               | (args1,ctrl4) ->
                                                   ret
                                                     ((let uu___141_7205 = t3
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           (FStar_Syntax_Syntax.Tm_app
                                                              (hd2, args1));
                                                         FStar_Syntax_Syntax.pos
                                                           =
                                                           (uu___141_7205.FStar_Syntax_Syntax.pos);
                                                         FStar_Syntax_Syntax.vars
                                                           =
                                                           (uu___141_7205.FStar_Syntax_Syntax.vars)
                                                       }), ctrl4)))
                             | FStar_Syntax_Syntax.Tm_abs (bs,t4,k) ->
                                 let uu____7231 =
                                   FStar_Syntax_Subst.open_term bs t4  in
                                 (match uu____7231 with
                                  | (bs1,t') ->
                                      let uu____7246 =
                                        let uu____7253 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1
                                           in
                                        ctrl_tac_fold f uu____7253 ctrl1 t'
                                         in
                                      bind uu____7246
                                        (fun uu____7271  ->
                                           match uu____7271 with
                                           | (t'',ctrl2) ->
                                               let uu____7286 =
                                                 let uu____7293 =
                                                   let uu___142_7296 = t4  in
                                                   let uu____7299 =
                                                     let uu____7300 =
                                                       let uu____7317 =
                                                         FStar_Syntax_Subst.close_binders
                                                           bs1
                                                          in
                                                       let uu____7318 =
                                                         FStar_Syntax_Subst.close
                                                           bs1 t''
                                                          in
                                                       (uu____7317,
                                                         uu____7318, k)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____7300
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       uu____7299;
                                                     FStar_Syntax_Syntax.pos
                                                       =
                                                       (uu___142_7296.FStar_Syntax_Syntax.pos);
                                                     FStar_Syntax_Syntax.vars
                                                       =
                                                       (uu___142_7296.FStar_Syntax_Syntax.vars)
                                                   }  in
                                                 (uu____7293, ctrl2)  in
                                               ret uu____7286))
                             | FStar_Syntax_Syntax.Tm_arrow (bs,k) ->
                                 ret (t3, ctrl1)
                             | uu____7351 -> ret (t3, ctrl1))))

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
              let uu____7402 = ctrl_tac_fold f env ctrl t  in
              bind uu____7402
                (fun uu____7430  ->
                   match uu____7430 with
                   | (t1,ctrl1) ->
                       let uu____7449 = ctrl_tac_fold_args f env ctrl1 ts1
                          in
                       bind uu____7449
                         (fun uu____7480  ->
                            match uu____7480 with
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
              let uu____7576 =
                let uu____7583 =
                  add_irrelevant_goal "dummy" env FStar_Syntax_Util.t_true
                    opts
                   in
                bind uu____7583
                  (fun uu____7592  ->
                     let uu____7593 = ctrl t1  in
                     bind uu____7593
                       (fun res  ->
                          let uu____7616 = trivial ()  in
                          bind uu____7616 (fun uu____7624  -> ret res)))
                 in
              bind uu____7576
                (fun uu____7640  ->
                   match uu____7640 with
                   | (should_rewrite,ctrl1) ->
                       if Prims.op_Negation should_rewrite
                       then ret (t1, ctrl1)
                       else
                         (let uu____7664 =
                            FStar_TypeChecker_TcTerm.tc_term env t1  in
                          match uu____7664 with
                          | (t2,lcomp,g) ->
                              let uu____7680 =
                                (let uu____7683 =
                                   FStar_Syntax_Util.is_pure_or_ghost_lcomp
                                     lcomp
                                    in
                                 Prims.op_Negation uu____7683) ||
                                  (let uu____7685 =
                                     FStar_TypeChecker_Rel.is_trivial g  in
                                   Prims.op_Negation uu____7685)
                                 in
                              if uu____7680
                              then ret (t2, globalStop)
                              else
                                (let typ = lcomp.FStar_Syntax_Syntax.res_typ
                                    in
                                 let uu____7698 =
                                   new_uvar "pointwise_rec" env typ  in
                                 bind uu____7698
                                   (fun ut  ->
                                      log ps
                                        (fun uu____7713  ->
                                           let uu____7714 =
                                             FStar_Syntax_Print.term_to_string
                                               t2
                                              in
                                           let uu____7715 =
                                             FStar_Syntax_Print.term_to_string
                                               ut
                                              in
                                           FStar_Util.print2
                                             "Pointwise_rec: making equality\n\t%s ==\n\t%s\n"
                                             uu____7714 uu____7715);
                                      (let uu____7716 =
                                         let uu____7719 =
                                           let uu____7720 =
                                             FStar_TypeChecker_TcTerm.universe_of
                                               env typ
                                              in
                                           FStar_Syntax_Util.mk_eq2
                                             uu____7720 typ t2 ut
                                            in
                                         add_irrelevant_goal
                                           "rewrite_rec equation" env
                                           uu____7719 opts
                                          in
                                       bind uu____7716
                                         (fun uu____7727  ->
                                            let uu____7728 =
                                              bind rewriter
                                                (fun uu____7742  ->
                                                   let ut1 =
                                                     FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                                       env ut
                                                      in
                                                   log ps
                                                     (fun uu____7748  ->
                                                        let uu____7749 =
                                                          FStar_Syntax_Print.term_to_string
                                                            t2
                                                           in
                                                        let uu____7750 =
                                                          FStar_Syntax_Print.term_to_string
                                                            ut1
                                                           in
                                                        FStar_Util.print2
                                                          "rewrite_rec: succeeded rewriting\n\t%s to\n\t%s\n"
                                                          uu____7749
                                                          uu____7750);
                                                   ret (ut1, ctrl1))
                                               in
                                            focus uu____7728))))))
  
let (topdown_rewrite :
  (FStar_Syntax_Syntax.term ->
     (Prims.bool,FStar_BigInt.t) FStar_Pervasives_Native.tuple2 tac)
    -> unit tac -> unit tac)
  =
  fun ctrl  ->
    fun rewriter  ->
      bind get
        (fun ps  ->
           let uu____7798 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7798 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7835  ->
                     let uu____7836 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Topdown_rewrite starting with %s\n"
                       uu____7836);
                bind dismiss_all
                  (fun uu____7839  ->
                     let uu____7840 =
                       ctrl_tac_fold
                         (rewrite_rec ps ctrl rewriter
                            g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context keepGoing gt1
                        in
                     bind uu____7840
                       (fun uu____7858  ->
                          match uu____7858 with
                          | (gt',uu____7866) ->
                              (log ps
                                 (fun uu____7870  ->
                                    let uu____7871 =
                                      FStar_Syntax_Print.term_to_string gt'
                                       in
                                    FStar_Util.print1
                                      "Topdown_rewrite seems to have succeded with %s\n"
                                      uu____7871);
                               (let uu____7872 = push_goals gs  in
                                bind uu____7872
                                  (fun uu____7876  ->
                                     add_goals
                                       [(let uu___144_7878 = g  in
                                         {
                                           FStar_Tactics_Types.context =
                                             (uu___144_7878.FStar_Tactics_Types.context);
                                           FStar_Tactics_Types.witness =
                                             (uu___144_7878.FStar_Tactics_Types.witness);
                                           FStar_Tactics_Types.goal_ty = gt';
                                           FStar_Tactics_Types.opts =
                                             (uu___144_7878.FStar_Tactics_Types.opts);
                                           FStar_Tactics_Types.is_guard =
                                             (uu___144_7878.FStar_Tactics_Types.is_guard)
                                         })])))))))
  
let (pointwise : FStar_Tactics_Types.direction -> unit tac -> unit tac) =
  fun d  ->
    fun tau  ->
      bind get
        (fun ps  ->
           let uu____7904 =
             match ps.FStar_Tactics_Types.goals with
             | g::gs -> (g, gs)
             | [] -> failwith "Pointwise: no goals"  in
           match uu____7904 with
           | (g,gs) ->
               let gt1 = g.FStar_Tactics_Types.goal_ty  in
               (log ps
                  (fun uu____7941  ->
                     let uu____7942 = FStar_Syntax_Print.term_to_string gt1
                        in
                     FStar_Util.print1 "Pointwise starting with %s\n"
                       uu____7942);
                bind dismiss_all
                  (fun uu____7945  ->
                     let uu____7946 =
                       tac_fold_env d
                         (pointwise_rec ps tau g.FStar_Tactics_Types.opts)
                         g.FStar_Tactics_Types.context gt1
                        in
                     bind uu____7946
                       (fun gt'  ->
                          log ps
                            (fun uu____7956  ->
                               let uu____7957 =
                                 FStar_Syntax_Print.term_to_string gt'  in
                               FStar_Util.print1
                                 "Pointwise seems to have succeded with %s\n"
                                 uu____7957);
                          (let uu____7958 = push_goals gs  in
                           bind uu____7958
                             (fun uu____7962  ->
                                add_goals
                                  [(let uu___145_7964 = g  in
                                    {
                                      FStar_Tactics_Types.context =
                                        (uu___145_7964.FStar_Tactics_Types.context);
                                      FStar_Tactics_Types.witness =
                                        (uu___145_7964.FStar_Tactics_Types.witness);
                                      FStar_Tactics_Types.goal_ty = gt';
                                      FStar_Tactics_Types.opts =
                                        (uu___145_7964.FStar_Tactics_Types.opts);
                                      FStar_Tactics_Types.is_guard =
                                        (uu___145_7964.FStar_Tactics_Types.is_guard)
                                    })]))))))
  
let (trefl : unit -> unit tac) =
  fun uu____7971  ->
    let uu____7974 = cur_goal ()  in
    bind uu____7974
      (fun g  ->
         let uu____7992 =
           FStar_Syntax_Util.un_squash g.FStar_Tactics_Types.goal_ty  in
         match uu____7992 with
         | FStar_Pervasives_Native.Some t ->
             let uu____8004 = FStar_Syntax_Util.head_and_args' t  in
             (match uu____8004 with
              | (hd1,args) ->
                  let uu____8037 =
                    let uu____8050 =
                      let uu____8051 = FStar_Syntax_Util.un_uinst hd1  in
                      uu____8051.FStar_Syntax_Syntax.n  in
                    (uu____8050, args)  in
                  (match uu____8037 with
                   | (FStar_Syntax_Syntax.Tm_fvar
                      fv,uu____8065::(l,uu____8067)::(r,uu____8069)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.eq2_lid
                       ->
                       let uu____8116 =
                         do_unify g.FStar_Tactics_Types.context l r  in
                       bind uu____8116
                         (fun b  ->
                            if Prims.op_Negation b
                            then
                              let uu____8125 =
                                tts g.FStar_Tactics_Types.context l  in
                              let uu____8126 =
                                tts g.FStar_Tactics_Types.context r  in
                              fail2
                                "trefl: not a trivial equality (%s vs %s)"
                                uu____8125 uu____8126
                            else solve g FStar_Syntax_Util.exp_unit)
                   | (hd2,uu____8129) ->
                       let uu____8146 = tts g.FStar_Tactics_Types.context t
                          in
                       fail1 "trefl: not an equality (%s)" uu____8146))
         | FStar_Pervasives_Native.None  -> fail "not an irrelevant goal")
  
let (dup : unit -> unit tac) =
  fun uu____8155  ->
    let uu____8158 = cur_goal ()  in
    bind uu____8158
      (fun g  ->
         let uu____8164 =
           new_uvar "dup" g.FStar_Tactics_Types.context
             g.FStar_Tactics_Types.goal_ty
            in
         bind uu____8164
           (fun u  ->
              let g' =
                let uu___146_8171 = g  in
                {
                  FStar_Tactics_Types.context =
                    (uu___146_8171.FStar_Tactics_Types.context);
                  FStar_Tactics_Types.witness = u;
                  FStar_Tactics_Types.goal_ty =
                    (uu___146_8171.FStar_Tactics_Types.goal_ty);
                  FStar_Tactics_Types.opts =
                    (uu___146_8171.FStar_Tactics_Types.opts);
                  FStar_Tactics_Types.is_guard =
                    (uu___146_8171.FStar_Tactics_Types.is_guard)
                }  in
              bind __dismiss
                (fun uu____8174  ->
                   let uu____8175 =
                     let uu____8178 =
                       let uu____8179 =
                         FStar_TypeChecker_TcTerm.universe_of
                           g.FStar_Tactics_Types.context
                           g.FStar_Tactics_Types.goal_ty
                          in
                       FStar_Syntax_Util.mk_eq2 uu____8179
                         g.FStar_Tactics_Types.goal_ty u
                         g.FStar_Tactics_Types.witness
                        in
                     add_irrelevant_goal "dup equation"
                       g.FStar_Tactics_Types.context uu____8178
                       g.FStar_Tactics_Types.opts
                      in
                   bind uu____8175
                     (fun uu____8182  ->
                        let uu____8183 = add_goals [g']  in
                        bind uu____8183 (fun uu____8187  -> ret ())))))
  
let (flip : unit -> unit tac) =
  fun uu____8194  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             set
               (let uu___147_8211 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___147_8211.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___147_8211.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___147_8211.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (g2 :: g1 :: gs);
                  FStar_Tactics_Types.smt_goals =
                    (uu___147_8211.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___147_8211.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___147_8211.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___147_8211.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___147_8211.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___147_8211.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___147_8211.FStar_Tactics_Types.freshness)
                })
         | uu____8212 -> fail "flip: less than 2 goals")
  
let (later : unit -> unit tac) =
  fun uu____8221  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | g::gs ->
             set
               (let uu___148_8234 = ps  in
                {
                  FStar_Tactics_Types.main_context =
                    (uu___148_8234.FStar_Tactics_Types.main_context);
                  FStar_Tactics_Types.main_goal =
                    (uu___148_8234.FStar_Tactics_Types.main_goal);
                  FStar_Tactics_Types.all_implicits =
                    (uu___148_8234.FStar_Tactics_Types.all_implicits);
                  FStar_Tactics_Types.goals = (FStar_List.append gs [g]);
                  FStar_Tactics_Types.smt_goals =
                    (uu___148_8234.FStar_Tactics_Types.smt_goals);
                  FStar_Tactics_Types.depth =
                    (uu___148_8234.FStar_Tactics_Types.depth);
                  FStar_Tactics_Types.__dump =
                    (uu___148_8234.FStar_Tactics_Types.__dump);
                  FStar_Tactics_Types.psc =
                    (uu___148_8234.FStar_Tactics_Types.psc);
                  FStar_Tactics_Types.entry_range =
                    (uu___148_8234.FStar_Tactics_Types.entry_range);
                  FStar_Tactics_Types.guard_policy =
                    (uu___148_8234.FStar_Tactics_Types.guard_policy);
                  FStar_Tactics_Types.freshness =
                    (uu___148_8234.FStar_Tactics_Types.freshness)
                }))
  
let (qed : unit -> unit tac) =
  fun uu____8241  ->
    bind get
      (fun ps  ->
         match ps.FStar_Tactics_Types.goals with
         | [] -> ret ()
         | uu____8248 -> fail "Not done!")
  
let (cases :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2 tac)
  =
  fun t  ->
    let uu____8268 =
      let uu____8275 = cur_goal ()  in
      bind uu____8275
        (fun g  ->
           let uu____8285 = __tc g.FStar_Tactics_Types.context t  in
           bind uu____8285
             (fun uu____8321  ->
                match uu____8321 with
                | (t1,typ,guard) ->
                    let uu____8337 = FStar_Syntax_Util.head_and_args typ  in
                    (match uu____8337 with
                     | (hd1,args) ->
                         let uu____8380 =
                           let uu____8393 =
                             let uu____8394 = FStar_Syntax_Util.un_uinst hd1
                                in
                             uu____8394.FStar_Syntax_Syntax.n  in
                           (uu____8393, args)  in
                         (match uu____8380 with
                          | (FStar_Syntax_Syntax.Tm_fvar
                             fv,(p,uu____8413)::(q,uu____8415)::[]) when
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
                                let uu___149_8453 = g  in
                                let uu____8454 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_p
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8454;
                                  FStar_Tactics_Types.witness =
                                    (uu___149_8453.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___149_8453.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___149_8453.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___149_8453.FStar_Tactics_Types.is_guard)
                                }  in
                              let g2 =
                                let uu___150_8456 = g  in
                                let uu____8457 =
                                  FStar_TypeChecker_Env.push_bv
                                    g.FStar_Tactics_Types.context v_q
                                   in
                                {
                                  FStar_Tactics_Types.context = uu____8457;
                                  FStar_Tactics_Types.witness =
                                    (uu___150_8456.FStar_Tactics_Types.witness);
                                  FStar_Tactics_Types.goal_ty =
                                    (uu___150_8456.FStar_Tactics_Types.goal_ty);
                                  FStar_Tactics_Types.opts =
                                    (uu___150_8456.FStar_Tactics_Types.opts);
                                  FStar_Tactics_Types.is_guard =
                                    (uu___150_8456.FStar_Tactics_Types.is_guard)
                                }  in
                              bind __dismiss
                                (fun uu____8464  ->
                                   let uu____8465 = add_goals [g1; g2]  in
                                   bind uu____8465
                                     (fun uu____8474  ->
                                        let uu____8475 =
                                          let uu____8480 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_p
                                             in
                                          let uu____8481 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              v_q
                                             in
                                          (uu____8480, uu____8481)  in
                                        ret uu____8475))
                          | uu____8486 ->
                              let uu____8499 =
                                tts g.FStar_Tactics_Types.context typ  in
                              fail1 "Not a disjunction: %s" uu____8499))))
       in
    FStar_All.pipe_left (wrap_err "cases") uu____8268
  
let (set_options : Prims.string -> unit tac) =
  fun s  ->
    let uu____8529 = cur_goal ()  in
    bind uu____8529
      (fun g  ->
         FStar_Options.push ();
         (let uu____8542 = FStar_Util.smap_copy g.FStar_Tactics_Types.opts
             in
          FStar_Options.set uu____8542);
         (let res = FStar_Options.set_options FStar_Options.Set s  in
          let opts' = FStar_Options.peek ()  in
          FStar_Options.pop ();
          (match res with
           | FStar_Getopt.Success  ->
               let g' =
                 let uu___151_8549 = g  in
                 {
                   FStar_Tactics_Types.context =
                     (uu___151_8549.FStar_Tactics_Types.context);
                   FStar_Tactics_Types.witness =
                     (uu___151_8549.FStar_Tactics_Types.witness);
                   FStar_Tactics_Types.goal_ty =
                     (uu___151_8549.FStar_Tactics_Types.goal_ty);
                   FStar_Tactics_Types.opts = opts';
                   FStar_Tactics_Types.is_guard =
                     (uu___151_8549.FStar_Tactics_Types.is_guard)
                 }  in
               replace_cur g'
           | FStar_Getopt.Error err ->
               fail2 "Setting options `%s` failed: %s" s err
           | FStar_Getopt.Help  ->
               fail1 "Setting options `%s` failed (got `Help`?)" s)))
  
let (top_env : unit -> env tac) =
  fun uu____8557  ->
    bind get
      (fun ps  -> FStar_All.pipe_left ret ps.FStar_Tactics_Types.main_context)
  
let (cur_env : unit -> env tac) =
  fun uu____8570  ->
    let uu____8573 = cur_goal ()  in
    bind uu____8573
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.context)
  
let (cur_goal' : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8586  ->
    let uu____8589 = cur_goal ()  in
    bind uu____8589
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.goal_ty)
  
let (cur_witness : unit -> FStar_Syntax_Syntax.term tac) =
  fun uu____8602  ->
    let uu____8605 = cur_goal ()  in
    bind uu____8605
      (fun g  -> FStar_All.pipe_left ret g.FStar_Tactics_Types.witness)
  
let (unquote :
  FStar_Reflection_Data.typ ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term tac)
  =
  fun ty  ->
    fun tm  ->
      let uu____8626 =
        let uu____8629 = cur_goal ()  in
        bind uu____8629
          (fun goal  ->
             let env =
               FStar_TypeChecker_Env.set_expected_typ
                 goal.FStar_Tactics_Types.context ty
                in
             let uu____8637 = __tc env tm  in
             bind uu____8637
               (fun uu____8657  ->
                  match uu____8657 with
                  | (tm1,typ,guard) ->
                      let uu____8669 =
                        proc_guard "unquote" env guard
                          goal.FStar_Tactics_Types.opts
                         in
                      bind uu____8669 (fun uu____8673  -> ret tm1)))
         in
      FStar_All.pipe_left (wrap_err "unquote") uu____8626
  
let (uvar_env :
  env ->
    FStar_Reflection_Data.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term tac)
  =
  fun env  ->
    fun ty  ->
      let uu____8696 =
        match ty with
        | FStar_Pervasives_Native.Some ty1 -> ret ty1
        | FStar_Pervasives_Native.None  ->
            let uu____8702 =
              let uu____8703 = FStar_Syntax_Util.type_u ()  in
              FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8703  in
            new_uvar "uvar_env.2" env uu____8702
         in
      bind uu____8696
        (fun typ  ->
           let uu____8715 = new_uvar "uvar_env" env typ  in
           bind uu____8715 (fun t  -> ret t))
  
let (unshelve : FStar_Syntax_Syntax.term -> unit tac) =
  fun t  ->
    let uu____8729 =
      bind get
        (fun ps  ->
           let env = ps.FStar_Tactics_Types.main_context  in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu____8746 -> g.FStar_Tactics_Types.opts
             | uu____8749 -> FStar_Options.peek ()  in
           let uu____8752 = FStar_Syntax_Util.head_and_args t  in
           match uu____8752 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (uu____8769,typ);
                FStar_Syntax_Syntax.pos = uu____8771;
                FStar_Syntax_Syntax.vars = uu____8772;_},uu____8773)
               ->
               let uu____8818 =
                 let uu____8821 =
                   let uu____8822 = bnorm env t  in
                   let uu____8823 = bnorm env typ  in
                   {
                     FStar_Tactics_Types.context = env;
                     FStar_Tactics_Types.witness = uu____8822;
                     FStar_Tactics_Types.goal_ty = uu____8823;
                     FStar_Tactics_Types.opts = opts;
                     FStar_Tactics_Types.is_guard = false
                   }  in
                 [uu____8821]  in
               add_goals uu____8818
           | uu____8824 -> fail "not a uvar")
       in
    FStar_All.pipe_left (wrap_err "unshelve") uu____8729
  
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
          (fun uu____8885  ->
             let uu____8886 = FStar_Options.unsafe_tactic_exec ()  in
             if uu____8886
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
        (fun uu____8907  ->
           let uu____8908 =
             FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None t  in
           ret uu____8908)
  
let (change : FStar_Reflection_Data.typ -> unit tac) =
  fun ty  ->
    let uu____8918 =
      mlog
        (fun uu____8923  ->
           let uu____8924 = FStar_Syntax_Print.term_to_string ty  in
           FStar_Util.print1 "change: ty = %s\n" uu____8924)
        (fun uu____8927  ->
           let uu____8928 = cur_goal ()  in
           bind uu____8928
             (fun g  ->
                let uu____8934 = __tc g.FStar_Tactics_Types.context ty  in
                bind uu____8934
                  (fun uu____8954  ->
                     match uu____8954 with
                     | (ty1,uu____8964,guard) ->
                         let uu____8966 =
                           proc_guard "change" g.FStar_Tactics_Types.context
                             guard g.FStar_Tactics_Types.opts
                            in
                         bind uu____8966
                           (fun uu____8971  ->
                              let uu____8972 =
                                do_unify g.FStar_Tactics_Types.context
                                  g.FStar_Tactics_Types.goal_ty ty1
                                 in
                              bind uu____8972
                                (fun bb  ->
                                   if bb
                                   then
                                     replace_cur
                                       (let uu___152_8981 = g  in
                                        {
                                          FStar_Tactics_Types.context =
                                            (uu___152_8981.FStar_Tactics_Types.context);
                                          FStar_Tactics_Types.witness =
                                            (uu___152_8981.FStar_Tactics_Types.witness);
                                          FStar_Tactics_Types.goal_ty = ty1;
                                          FStar_Tactics_Types.opts =
                                            (uu___152_8981.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (uu___152_8981.FStar_Tactics_Types.is_guard)
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
                                      let uu____8988 =
                                        do_unify
                                          g.FStar_Tactics_Types.context ng
                                          nty
                                         in
                                      bind uu____8988
                                        (fun b  ->
                                           if b
                                           then
                                             replace_cur
                                               (let uu___153_8997 = g  in
                                                {
                                                  FStar_Tactics_Types.context
                                                    =
                                                    (uu___153_8997.FStar_Tactics_Types.context);
                                                  FStar_Tactics_Types.witness
                                                    =
                                                    (uu___153_8997.FStar_Tactics_Types.witness);
                                                  FStar_Tactics_Types.goal_ty
                                                    = ty1;
                                                  FStar_Tactics_Types.opts =
                                                    (uu___153_8997.FStar_Tactics_Types.opts);
                                                  FStar_Tactics_Types.is_guard
                                                    =
                                                    (uu___153_8997.FStar_Tactics_Types.is_guard)
                                                })
                                           else fail "not convertible")))))))
       in
    FStar_All.pipe_left (wrap_err "change") uu____8918
  
let rec last : 'a . 'a Prims.list -> 'a =
  fun l  ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____9019::xs -> last xs
  
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l  ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____9047 = init xs  in x :: uu____9047
  
let rec (inspect :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view tac) =
  fun t  ->
    let t1 = FStar_Syntax_Util.unascribe t  in
    let t2 = FStar_Syntax_Util.un_uinst t1  in
    match t2.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t3,uu____9064) -> inspect t3
    | FStar_Syntax_Syntax.Tm_name bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Var bv)
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_BVar bv)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_FVar fv)
    | FStar_Syntax_Syntax.Tm_app (hd1,[]) ->
        failwith "inspect: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9121 = last args  in
        (match uu____9121 with
         | (a,q) ->
             let q' = FStar_Reflection_Basic.inspect_aqual q  in
             let uu____9143 =
               let uu____9144 =
                 let uu____9149 =
                   let uu____9152 =
                     let uu____9157 = init args  in
                     FStar_Syntax_Syntax.mk_Tm_app hd1 uu____9157  in
                   uu____9152 FStar_Pervasives_Native.None
                     t2.FStar_Syntax_Syntax.pos
                    in
                 (uu____9149, (a, q'))  in
               FStar_Reflection_Data.Tv_App uu____9144  in
             FStar_All.pipe_left ret uu____9143)
    | FStar_Syntax_Syntax.Tm_abs ([],uu____9178,uu____9179) ->
        failwith "inspect: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (bs,t3,k) ->
        let uu____9223 = FStar_Syntax_Subst.open_term bs t3  in
        (match uu____9223 with
         | (bs1,t4) ->
             (match bs1 with
              | [] -> failwith "impossible"
              | b::bs2 ->
                  let uu____9256 =
                    let uu____9257 =
                      let uu____9262 = FStar_Syntax_Util.abs bs2 t4 k  in
                      (b, uu____9262)  in
                    FStar_Reflection_Data.Tv_Abs uu____9257  in
                  FStar_All.pipe_left ret uu____9256))
    | FStar_Syntax_Syntax.Tm_type uu____9269 ->
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Type ())
    | FStar_Syntax_Syntax.Tm_arrow ([],k) ->
        failwith "inspect: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____9289 ->
        let uu____9302 = FStar_Syntax_Util.arrow_one t2  in
        (match uu____9302 with
         | FStar_Pervasives_Native.Some (b,c) ->
             FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Arrow (b, c))
         | FStar_Pervasives_Native.None  -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv,t3) ->
        let b = FStar_Syntax_Syntax.mk_binder bv  in
        let uu____9332 = FStar_Syntax_Subst.open_term [b] t3  in
        (match uu____9332 with
         | (b',t4) ->
             let b1 =
               match b' with
               | b'1::[] -> b'1
               | uu____9363 -> failwith "impossible"  in
             FStar_All.pipe_left ret
               (FStar_Reflection_Data.Tv_Refine
                  ((FStar_Pervasives_Native.fst b1), t4)))
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____9371 =
          let uu____9372 = FStar_Reflection_Basic.inspect_const c  in
          FStar_Reflection_Data.Tv_Const uu____9372  in
        FStar_All.pipe_left ret uu____9371
    | FStar_Syntax_Syntax.Tm_uvar (u,t3) ->
        let uu____9401 =
          let uu____9402 =
            let uu____9407 =
              let uu____9408 = FStar_Syntax_Unionfind.uvar_id u  in
              FStar_BigInt.of_int_fs uu____9408  in
            (uu____9407, t3)  in
          FStar_Reflection_Data.Tv_Uvar uu____9402  in
        FStar_All.pipe_left ret uu____9401
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____9436 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let b = FStar_Syntax_Syntax.mk_binder bv  in
               let uu____9441 = FStar_Syntax_Subst.open_term [b] t21  in
               (match uu____9441 with
                | (bs,t22) ->
                    let b1 =
                      match bs with
                      | b1::[] -> b1
                      | uu____9472 ->
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
           | FStar_Util.Inr uu____9504 ->
               FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               let uu____9508 = FStar_Syntax_Subst.open_let_rec [lb] t21  in
               (match uu____9508 with
                | (lbs,t22) ->
                    (match lbs with
                     | lb1::[] ->
                         (match lb1.FStar_Syntax_Syntax.lbname with
                          | FStar_Util.Inr uu____9528 ->
                              ret FStar_Reflection_Data.Tv_Unknown
                          | FStar_Util.Inl bv1 ->
                              FStar_All.pipe_left ret
                                (FStar_Reflection_Data.Tv_Let
                                   (true, bv1,
                                     (lb1.FStar_Syntax_Syntax.lbdef), t22)))
                     | uu____9534 ->
                         failwith
                           "impossible: open_term returned different amount of binders")))
    | FStar_Syntax_Syntax.Tm_match (t3,brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____9588 = FStar_Reflection_Basic.inspect_const c  in
              FStar_Reflection_Data.Pat_Constant uu____9588
          | FStar_Syntax_Syntax.Pat_cons (fv,ps) ->
              let uu____9607 =
                let uu____9614 =
                  FStar_List.map
                    (fun uu____9626  ->
                       match uu____9626 with
                       | (p1,uu____9634) -> inspect_pat p1) ps
                   in
                (fv, uu____9614)  in
              FStar_Reflection_Data.Pat_Cons uu____9607
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
            (fun uu___87_9688  ->
               match uu___87_9688 with
               | (pat,uu____9710,t4) ->
                   let uu____9728 = inspect_pat pat  in (uu____9728, t4))
            brs1
           in
        FStar_All.pipe_left ret (FStar_Reflection_Data.Tv_Match (t3, brs2))
    | FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown
    | uu____9745 ->
        ((let uu____9747 =
            let uu____9752 =
              let uu____9753 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____9754 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.format2
                "inspect: outside of expected syntax (%s, %s)\n" uu____9753
                uu____9754
               in
            (FStar_Errors.Warning_CantInspect, uu____9752)  in
          FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____9747);
         FStar_All.pipe_left ret FStar_Reflection_Data.Tv_Unknown)
  
let (pack : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term tac)
  =
  fun tv  ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv ->
        let uu____9767 = FStar_Syntax_Syntax.bv_to_name bv  in
        FStar_All.pipe_left ret uu____9767
    | FStar_Reflection_Data.Tv_BVar bv ->
        let uu____9771 = FStar_Syntax_Syntax.bv_to_tm bv  in
        FStar_All.pipe_left ret uu____9771
    | FStar_Reflection_Data.Tv_FVar fv ->
        let uu____9775 = FStar_Syntax_Syntax.fv_to_tm fv  in
        FStar_All.pipe_left ret uu____9775
    | FStar_Reflection_Data.Tv_App (l,(r,q)) ->
        let q' = FStar_Reflection_Basic.pack_aqual q  in
        let uu____9786 = FStar_Syntax_Util.mk_app l [(r, q')]  in
        FStar_All.pipe_left ret uu____9786
    | FStar_Reflection_Data.Tv_Abs (b,t) ->
        let uu____9807 =
          FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None  in
        FStar_All.pipe_left ret uu____9807
    | FStar_Reflection_Data.Tv_Arrow (b,c) ->
        let uu____9812 = FStar_Syntax_Util.arrow [b] c  in
        FStar_All.pipe_left ret uu____9812
    | FStar_Reflection_Data.Tv_Type () ->
        FStar_All.pipe_left ret FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv,t) ->
        let uu____9827 = FStar_Syntax_Util.refine bv t  in
        FStar_All.pipe_left ret uu____9827
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____9839 =
          let uu____9842 =
            let uu____9849 =
              let uu____9850 = FStar_Reflection_Basic.pack_const c  in
              FStar_Syntax_Syntax.Tm_constant uu____9850  in
            FStar_Syntax_Syntax.mk uu____9849  in
          uu____9842 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9839
    | FStar_Reflection_Data.Tv_Uvar (u,t) ->
        let uu____9864 =
          let uu____9867 = FStar_BigInt.to_int_fs u  in
          FStar_Syntax_Util.uvar_from_id uu____9867 t  in
        FStar_All.pipe_left ret uu____9864
    | FStar_Reflection_Data.Tv_Let (false ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9882 =
          let uu____9885 =
            let uu____9892 =
              let uu____9893 =
                let uu____9906 =
                  let uu____9907 =
                    let uu____9908 = FStar_Syntax_Syntax.mk_binder bv  in
                    [uu____9908]  in
                  FStar_Syntax_Subst.close uu____9907 t2  in
                ((false, [lb]), uu____9906)  in
              FStar_Syntax_Syntax.Tm_let uu____9893  in
            FStar_Syntax_Syntax.mk uu____9892  in
          uu____9885 FStar_Pervasives_Native.None FStar_Range.dummyRange  in
        FStar_All.pipe_left ret uu____9882
    | FStar_Reflection_Data.Tv_Let (true ,bv,t1,t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            [] FStar_Range.dummyRange
           in
        let uu____9934 = FStar_Syntax_Subst.close_let_rec [lb] t2  in
        (match uu____9934 with
         | (lbs,body) ->
             let uu____9949 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_let ((true, lbs), body))
                 FStar_Pervasives_Native.None FStar_Range.dummyRange
                in
             FStar_All.pipe_left ret uu____9949)
    | FStar_Reflection_Data.Tv_Match (t,brs) ->
        let wrap v1 =
          {
            FStar_Syntax_Syntax.v = v1;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          }  in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____9989 =
                let uu____9990 = FStar_Reflection_Basic.pack_const c  in
                FStar_Syntax_Syntax.Pat_constant uu____9990  in
              FStar_All.pipe_left wrap uu____9989
          | FStar_Reflection_Data.Pat_Cons (fv,ps) ->
              let uu____9999 =
                let uu____10000 =
                  let uu____10013 =
                    FStar_List.map
                      (fun p1  ->
                         let uu____10027 = pack_pat p1  in
                         (uu____10027, false)) ps
                     in
                  (fv, uu____10013)  in
                FStar_Syntax_Syntax.Pat_cons uu____10000  in
              FStar_All.pipe_left wrap uu____9999
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
            (fun uu___88_10077  ->
               match uu___88_10077 with
               | (pat,t1) ->
                   let uu____10094 = pack_pat pat  in
                   (uu____10094, FStar_Pervasives_Native.None, t1)) brs
           in
        let brs2 = FStar_List.map FStar_Syntax_Subst.close_branch brs1  in
        let uu____10104 =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs2))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10104
    | FStar_Reflection_Data.Tv_AscribedT (e,t,tacopt) ->
        let uu____10124 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inl t), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10124
    | FStar_Reflection_Data.Tv_AscribedC (e,c,tacopt) ->
        let uu____10166 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (e, ((FStar_Util.Inr c), tacopt),
                 FStar_Pervasives_Native.None)) FStar_Pervasives_Native.None
            FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10166
    | FStar_Reflection_Data.Tv_Unknown  ->
        let uu____10201 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        FStar_All.pipe_left ret uu____10201
  
let (goal_of_goal_ty :
  env ->
    FStar_Reflection_Data.typ ->
      (FStar_Tactics_Types.goal,FStar_TypeChecker_Env.guard_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun typ  ->
      let uu____10230 =
        FStar_TypeChecker_Util.new_implicit_var "proofstate_of_goal_ty"
          typ.FStar_Syntax_Syntax.pos env typ
         in
      match uu____10230 with
      | (u,uu____10248,g_u) ->
          let g =
            let uu____10263 = FStar_Options.peek ()  in
            {
              FStar_Tactics_Types.context = env;
              FStar_Tactics_Types.witness = u;
              FStar_Tactics_Types.goal_ty = typ;
              FStar_Tactics_Types.opts = uu____10263;
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
      let uu____10278 = goal_of_goal_ty env typ  in
      match uu____10278 with
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
  